{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.Thm.ThmT
--
-- Production  thmT  step function and the 10 Group I dispatch lemmas
-- (combinator defining equations: axI, axFst, axSnd, axConst, axComp,
-- axComp2, axLift, axPost, axFan, axKT).  The remaining 30 dispatch
-- lemmas are deferred to Sessions D-F as parameters of the inner
--  WithDispatch  module.
--
-- This file extends  BRA.Thm.StepProto  's 2-tag prototype to a full
-- 40-tag flat linear  IfLf  cascade.  Architecture:
--
--   thmT      = Rec O stepProto
--   stepProto = Fan discComb branchesTop IfLf
--     discComb     = Lift (Comp Fst Fst)
--     branchesTop  = Fan dispatch (Post Snd Pair) Pair
--     dispatch     = Fan checkTag1 branch1 IfLf
--       checkTagN  = Fan (Lift (KT tagCodeN)) (Lift Fst) TreeEq
--       branch_K   = Fan body_K next_K Pair    (1 <= K <= 39)
--       branch_40  = Fan body_40 fbBody Pair
--       next_K     = Fan checkTag_(K+1) branch_(K+1) IfLf
--
-- Body convention for Group I (and all 31 non-recursive primitives):
--   body_K = Lift Snd .  Output = reify(payload of encoding) = Snd a .
-- Body convention for the 9 recursive primitives:  extract from b.
--
-- Cascade-skip factoring:  one  cascadeSkip_K  helper per level.  At
-- tag M dispatch, apply  cascadeSkip_1, .., cascadeSkip_(M-1)  in
-- sequence (each O(1)), then the M-th hit (1 lemma).  Keeps Group I
-- proofs O(M) rather than O(M^2) total.
--
-- Design note (flat linear vs balanced):
--   Flat linear (40-deep IfLf cascade) chosen.  BRA's only equality
--   primitive on  Tree  is  TreeEq ; balanced binary search would
--   require synthesising an ordering combinator from scratch (none in
--   BRA), far heavier than 40 sequential  TreeEq  comparisons.
--
-- Constraints:
--   * All heavy combinator construction inside ONE  abstract  block.
--   * Tags >= suc zero (codified in BRA.Thm.Tag).
--   * Zero postulates, zero holes.

module BRA.Thm.ThmT where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.SubT using (subT ; subTDef)
open import BRA.Sb2  using (subT2 ; subTDef2 ; codedSubst2)
open import BRA.CodeCommutes using (codeCommutesFormula)
open import BRA.Thm.Tag

open import BRA.Thm.Parts.AxI
open import BRA.Thm.Parts.AxFst
open import BRA.Thm.Parts.AxSnd
open import BRA.Thm.Parts.AxConst
open import BRA.Thm.Parts.AxComp
open import BRA.Thm.Parts.AxComp2
open import BRA.Thm.Parts.AxLift
open import BRA.Thm.Parts.AxPost
open import BRA.Thm.Parts.AxFan
open import BRA.Thm.Parts.AxKT
open import BRA.Thm.Parts.AxRecLf
open import BRA.Thm.Parts.AxRecNd
open import BRA.Thm.Parts.AxRecPLf
open import BRA.Thm.Parts.AxRecPNd
open import BRA.Thm.Parts.AxIfLfL
open import BRA.Thm.Parts.AxIfLfN
open import BRA.Thm.Parts.AxTreeEqLL
open import BRA.Thm.Parts.AxTreeEqLN
open import BRA.Thm.Parts.AxTreeEqNL
open import BRA.Thm.Parts.AxTreeEqNN
open import BRA.Thm.Parts.AxGoodstein
open import BRA.Thm.Parts.AxRefl
open import BRA.Thm.Parts.RuleSym
open import BRA.Thm.Parts.RuleTrans
open import BRA.Thm.Parts.Cong1
open import BRA.Thm.Parts.CongL
open import BRA.Thm.Parts.CongR
open import BRA.Thm.Parts.AxEqTrans
open import BRA.Thm.Parts.AxEqCong1
open import BRA.Thm.Parts.AxEqCongL
open import BRA.Thm.Parts.AxEqCongR
open import BRA.Thm.Parts.AxK
open import BRA.Thm.Parts.AxS
open import BRA.Thm.Parts.AxNeg
open import BRA.Thm.Parts.AxExFalso
open import BRA.Thm.Parts.AxContrapos
open import BRA.Thm.Parts.Mp
open import BRA.Thm.Parts.RuleInst
open import BRA.Thm.Parts.RuleIndBT
open import BRA.Thm.Parts.AxFstLf
open import BRA.Thm.Parts.AxSndLf
open import BRA.Thm.Parts.AxIfLfLL
open import BRA.Thm.Parts.AxIfLfNL
open import BRA.Thm.Parts.RuleInst2

------------------------------------------------------------------------
-- Reified tag codes (40).  Defined OUTSIDE the abstract block so that
-- consumer-visible signatures can name them without forcing unfolding.

tagCode_axI         : Term
tagCode_axI         = reify (natCode tagAxI)
tagCode_axFst       : Term
tagCode_axFst       = reify (natCode tagAxFst)
tagCode_axSnd       : Term
tagCode_axSnd       = reify (natCode tagAxSnd)
tagCode_axConst     : Term
tagCode_axConst     = reify (natCode tagAxConst)
tagCode_axComp      : Term
tagCode_axComp      = reify (natCode tagAxComp)
tagCode_axComp2     : Term
tagCode_axComp2     = reify (natCode tagAxComp2)
tagCode_axLift      : Term
tagCode_axLift      = reify (natCode tagAxLift)
tagCode_axPost      : Term
tagCode_axPost      = reify (natCode tagAxPost)
tagCode_axFan       : Term
tagCode_axFan       = reify (natCode tagAxFan)
tagCode_axKT        : Term
tagCode_axKT        = reify (natCode tagAxKT)
tagCode_axRecLf     : Term
tagCode_axRecLf     = reify (natCode tagAxRecLf)
tagCode_axRecNd     : Term
tagCode_axRecNd     = reify (natCode tagAxRecNd)
tagCode_axRecPLf    : Term
tagCode_axRecPLf    = reify (natCode tagAxRecPLf)
tagCode_axRecPNd    : Term
tagCode_axRecPNd    = reify (natCode tagAxRecPNd)
tagCode_axIfLfL     : Term
tagCode_axIfLfL     = reify (natCode tagAxIfLfL)
tagCode_axIfLfN     : Term
tagCode_axIfLfN     = reify (natCode tagAxIfLfN)
tagCode_axTreeEqLL  : Term
tagCode_axTreeEqLL  = reify (natCode tagAxTreeEqLL)
tagCode_axTreeEqLN  : Term
tagCode_axTreeEqLN  = reify (natCode tagAxTreeEqLN)
tagCode_axTreeEqNL  : Term
tagCode_axTreeEqNL  = reify (natCode tagAxTreeEqNL)
tagCode_axTreeEqNN  : Term
tagCode_axTreeEqNN  = reify (natCode tagAxTreeEqNN)
tagCode_axGoodstein : Term
tagCode_axGoodstein = reify (natCode tagAxGoodstein)
tagCode_axRefl      : Term
tagCode_axRefl      = reify (natCode tagAxRefl)
tagCode_ruleSym     : Term
tagCode_ruleSym     = reify (natCode tagRuleSym)
tagCode_ruleTrans   : Term
tagCode_ruleTrans   = reify (natCode tagRuleTrans)
tagCode_cong1       : Term
tagCode_cong1       = reify (natCode tagCong1)
tagCode_congL       : Term
tagCode_congL       = reify (natCode tagCongL)
tagCode_congR       : Term
tagCode_congR       = reify (natCode tagCongR)
tagCode_axEqTrans   : Term
tagCode_axEqTrans   = reify (natCode tagAxEqTrans)
tagCode_axEqCong1   : Term
tagCode_axEqCong1   = reify (natCode tagAxEqCong1)
tagCode_axEqCongL   : Term
tagCode_axEqCongL   = reify (natCode tagAxEqCongL)
tagCode_axEqCongR   : Term
tagCode_axEqCongR   = reify (natCode tagAxEqCongR)
tagCode_axK         : Term
tagCode_axK         = reify (natCode tagAxK)
tagCode_axS         : Term
tagCode_axS         = reify (natCode tagAxS)
tagCode_axNeg       : Term
tagCode_axNeg       = reify (natCode tagAxNeg)
tagCode_axExFalso   : Term
tagCode_axExFalso   = reify (natCode tagAxExFalso)
tagCode_axContrapos : Term
tagCode_axContrapos = reify (natCode tagAxContrapos)
tagCode_mp          : Term
tagCode_mp          = reify (natCode tagMp)
tagCode_ruleInst    : Term
tagCode_ruleInst    = reify (natCode tagRuleInst)
tagCode_ruleIndBT   : Term
tagCode_ruleIndBT   = reify (natCode tagRuleIndBT)
tagCode_axFstLf     : Term
tagCode_axFstLf     = reify (natCode tagAxFstLf)
tagCode_axSndLf     : Term
tagCode_axSndLf     = reify (natCode tagAxSndLf)
tagCode_axIfLfLL    : Term
tagCode_axIfLfLL    = reify (natCode tagAxIfLfLL)
tagCode_axIfLfNL    : Term
tagCode_axIfLfNL    = reify (natCode tagAxIfLfNL)
tagCode_ruleInst2   : Term
tagCode_ruleInst2   = reify (natCode tagRuleInst2)

------------------------------------------------------------------------
-- Constants: leading natCode tags inside codeF1 / codeF2 trees, named
-- via dummy applications.  Avoids hand-counting  suc  chains.
--
--   codeF1 (Comp f g)    = nd (natCode 29) (...)   -- regardless of f, g
--   codeF1 (Comp2 h f g) = nd (natCode 30) (...)
--   codeF1 (KT t)        = nd (natCode 32) (...)
--   codeF2 (Lift f)      = nd (natCode 28) (...)
--   codeF2 (Post f h)    = nd (natCode 29) (...)
--   codeF2 (Fan h1 h2 h) = nd (natCode 30) (...)
-- so  leftT  followed by  reify  produces the leading-tag constants.

tagCode_compFunc    : Term
tagCode_compFunc    = reify (leftT (codeF1 (Comp I I)))
tagCode_comp2Func   : Term
tagCode_comp2Func   = reify (leftT (codeF1 (Comp2 IfLf I I)))
tagCode_zFunc       : Term
tagCode_zFunc       = reify (leftT (codeF1 Z))
tagCode_liftFunc    : Term
tagCode_liftFunc    = reify (leftT (codeF2 (Lift I)))
tagCode_postFunc    : Term
tagCode_postFunc    = reify (leftT (codeF2 (Post I IfLf)))
tagCode_fanFunc     : Term
tagCode_fanFunc     = reify (leftT (codeF2 (Fan IfLf IfLf IfLf)))
tagCode_recFunc     : Term
tagCode_recFunc     = reify (leftT (codeF1 (Rec O Pair)))
tagCode_recPFunc    : Term
tagCode_recPFunc    = reify (leftT (codeF2 (RecP Pair)))
tagCode_ifLfFunc    : Term
tagCode_ifLfFunc    = reify (leftT (codeF2 IfLf))
tagCode_treeEqFunc  : Term
tagCode_treeEqFunc  = reify (leftT (codeF2 TreeEq))

------------------------------------------------------------------------
-- Lift helpers (deduction-theorem combinators) used by lifted dispatchers
-- below.  These are pure axiom-based combinators built from axK, axS,
-- axEqTrans, axEqCong*, mp.

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

liftedRuleSym : (P : Formula) (a b : Term) ->
                Deriv (P imp atomic (eqn a b)) ->
                Deriv (P imp atomic (eqn b a))
liftedRuleSym P a b D =
  liftedAxEqTrans P a b a D (liftAxiom P (axRefl a))

liftedRuleTrans : (P : Formula) (a b c : Term) ->
                  Deriv (P imp atomic (eqn a b)) ->
                  Deriv (P imp atomic (eqn b c)) ->
                  Deriv (P imp atomic (eqn a c))
liftedRuleTrans P a b c D1 D2 =
  liftedAxEqTrans P b a c (liftedRuleSym P a b D1) D2

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

------------------------------------------------------------------------
-- Heavy block: combinators, helpers, cascade-skip lemmas, Group I
-- dispatch proofs.

abstract

  ------------------------------------------------------------------
  -- Sentinel body for the cascade tail (after branch_40).  Returns O.

  fbBody : Fun2
  fbBody = Lift (KT O)

  ------------------------------------------------------------------
  -- 40 body combinators.  All 31 non-recursive primitives use
  -- Lift Snd  (output = reify of payload).  The 9 recursive
  -- primitives use deeper extractions from  b  (recursion result).

  -- body_axI computes reify(outAxI t) = Pair (Pair KAp1 (Pair KCodeF1_I payT)) payT
  -- where KAp1 = reify tagAp1, KCodeF1_I = reify (codeF1 I), payT = Snd a.
  body_axI         : Fun2
  body_axI         =
    Fan (Fan (Lift (KT (reify tagAp1)))
             (Fan (Lift (KT (reify (codeF1 I))))
                  (Lift Snd)
                  Pair)
             Pair)
        (Lift Snd)
        Pair
  -- body_axFst computes reify(outAxFst a' b') =
  --   Pair (Pair K_a1 (Pair K_cf1F (Pair K_a2 (Pair K_cf2P payT)))) payAT
  -- where payT = Pair payAT payBT, payAT = Fst payT, K* are codeF1/codeF2 constants.
  body_axFst       : Fun2
  body_axFst       =
    Fan (Fan (Lift (KT (reify tagAp1)))
             (Fan (Lift (KT (reify (codeF1 Fst))))
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Lift Snd)
                            Pair)
                       Pair)
                  Pair)
             Pair)
        (Lift (Comp Fst Snd))
        Pair
  body_axSnd       : Fun2
  body_axSnd       =
    Fan (Fan (Lift (KT (reify tagAp1)))
             (Fan (Lift (KT (reify (codeF1 Snd))))
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (KT (reify (codeF2 Pair))))
                            (Lift Snd)
                            Pair)
                       Pair)
                  Pair)
             Pair)
        (Lift (Comp Snd Snd))
        Pair

  body_axConst     : Fun2
  body_axConst     =
    Fan (Fan (Lift (KT (reify tagAp2)))
             (Fan (Lift (KT (reify (codeF2 Const))))
                  (Lift Snd)
                  Pair)
             Pair)
        (Lift (Comp Fst Snd))
        Pair

  -- axComp f g t : LHS = ap1 (Comp f g) t , RHS = ap1 f (ap1 g t).
  --   payT = Pair cf (Pair cg ct).
  --   reify(LHS) = Pair K_a1 (Pair (Pair K_compTag (Pair cf cg)) ct)
  --   reify(RHS) = Pair K_a1 (Pair cf (Pair K_a1 (Pair cg ct)))
  body_axComp      : Fun2
  body_axComp      =
    Fan
      -- LHS-build
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Fan (Lift (KT tagCode_compFunc))
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd)))
                          Pair)
                     Pair)
                (Lift (Comp Snd (Comp Snd Snd)))
                Pair)
           Pair)
      -- RHS-build
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Lift (KT (reify tagAp1)))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Snd (Comp Snd Snd)))
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

  -- axComp2 h f g t : LHS = ap1 (Comp2 h f g) t , RHS = ap2 h (ap1 f t) (ap1 g t).
  --   payT depth 4: Pair ch (Pair cf (Pair cg ct)).
  body_axComp2     : Fun2
  body_axComp2     =
    Fan
      -- LHS-build: Pair K_a1 (Pair (Pair K_comp2Tag (Pair ch (Pair cf cg))) ct)
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Fan (Lift (KT tagCode_comp2Func))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                Pair)
           Pair)
      -- RHS-build: Pair K_a2 (Pair ch (Pair (Pair K_a1 (Pair cf ct)) (Pair K_a1 (Pair cg ct))))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Fan (Lift (KT (reify tagAp1)))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     (Fan (Lift (KT (reify tagAp1)))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

  -- axLift f a' b' : LHS = ap2 (Lift f) a' b' , RHS = ap1 f a'.
  --   payT depth 3: Pair cf (Pair payAT payBT).
  body_axLift      : Fun2
  body_axLift      =
    Fan
      -- LHS-build: Pair K_a2 (Pair (Pair K_liftTag cf) (Pair payAT payBT))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Fan (Lift (KT tagCode_liftFunc))
                     (Lift (Comp Fst Snd))
                     Pair)
                (Fan (Lift (Comp Fst (Comp Snd Snd)))
                     (Lift (Comp Snd (Comp Snd Snd)))
                     Pair)
                Pair)
           Pair)
      -- RHS-build: Pair K_a1 (Pair cf payAT)
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (Comp Fst Snd))
                (Lift (Comp Fst (Comp Snd Snd)))
                Pair)
           Pair)
      Pair

  -- axPost f h a' b' : LHS = ap2 (Post f h) a' b' , RHS = ap1 f (ap2 h a' b').
  --   payT depth 4: Pair cf (Pair ch (Pair payAT payBT)).
  body_axPost      : Fun2
  body_axPost      =
    Fan
      -- LHS-build: Pair K_a2 (Pair (Pair K_postTag (Pair cf ch)) (Pair payAT payBT))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Fan (Lift (KT tagCode_postFunc))
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd)))
                          Pair)
                     Pair)
                (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                     Pair)
                Pair)
           Pair)
      -- RHS-build: Pair K_a1 (Pair cf (Pair K_a2 (Pair ch (Pair payAT payBT))))
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      Pair

  -- axFan h1 h2 h a' b' : LHS = ap2 (Fan h1 h2 h) a' b' , RHS = ap2 h (ap2 h1 a' b') (ap2 h2 a' b').
  --   payT depth 5: Pair ch1 (Pair ch2 (Pair ch (Pair payAT payBT))).
  body_axFan       : Fun2
  body_axFan       =
    Fan
      -- LHS-build: Pair K_a2 (Pair (Pair K_fanTag (Pair ch1 (Pair ch2 ch))) (Pair payAT payBT))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Fan (Lift (KT tagCode_fanFunc))
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                     Pair)
                Pair)
           Pair)
      -- RHS-build: Pair K_a2 (Pair ch (Pair LHSh1 LHSh2)) where
      --   LHSh1 = Pair K_a2 (Pair ch1 (Pair payAT payBT))
      --   LHSh2 = Pair K_a2 (Pair ch2 (Pair payAT payBT))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                (Fan
                  -- LHSh1 build
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 Pair)
                            Pair)
                       Pair)
                  -- LHSh2 build
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
                Pair)
           Pair)
      Pair

  -- axZ x : LHS = ap1 Z x , RHS = O .
  --   payT depth 2: Pair payZTagged payXT
  --     where payZTagged = reify (codeF1 Z), payXT = reify (code x).
  --   reify(LHS) = Pair K_a1 (Pair payZTagged payXT) = Pair K_a1 payT
  --   reify(RHS) = O (= reify lf, code O = lf after redesign)
  body_axZ         : Fun2
  body_axZ         =
    Fan
      -- LHS-build: Pair K_a1 (Snd a) = Pair K_a1 payT
      (Fan (Lift (KT (reify tagAp1)))
           (Lift Snd)
           Pair)
      -- RHS-build: O
      (Lift (KT O))
      Pair
  -- axRecLf z s : LHS = ap1 (Rec z s) O , RHS = z .
  --   payT depth 2: Pair payZT payST.
  --   reify(LHS) = Pair K_a1 (Pair (Pair K_recTag payT) O)    -- code O = lf
  --   reify(RHS) = payZT (= Fst payT)
  body_axRecLf     : Fun2
  body_axRecLf     =
    Fan
      -- LHS-build
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Fan (Lift (KT tagCode_recFunc))
                     (Lift Snd)
                     Pair)
                (Lift (KT O))
                Pair)
           Pair)
      -- RHS-build
      (Lift (Comp Fst Snd))
      Pair
  -- axRecNd z s a b :
  --   LHS = ap1 (Rec z s) (ap2 Pair a b)
  --   RHS = ap2 s (ap2 Pair a b) (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b))
  --   payT depth 4: Pair payZT (Pair payST (Pair payAT payBT)).
  body_axRecNd     : Fun2
  body_axRecNd     =
    Fan
      -- LHS-build: Pair K_a1 (Pair (Pair K_rT (Pair payZT payST))
      --                              (Pair K_a2 (Pair K_pair (Pair payAT payBT))))
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Fan (Lift (KT tagCode_recFunc))
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd)))
                          Pair)
                     Pair)
                (Fan (Lift (KT (reify tagAp2)))
                     (Fan (Lift (KT (reify (codeF2 Pair))))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      -- RHS-build: Pair K_a2 (Pair payST (Pair sub1 sub2))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst (Comp Snd Snd)))
                (Fan
                    -- sub1: Pair K_a2 (Pair K_pair (Pair payAT payBT))
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                   Pair)
                              Pair)
                         Pair)
                    -- sub2: Pair K_a2 (Pair K_pair (Pair recA recB))
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan
                                  -- recA: Pair K_a1 (Pair (Pair K_rT (Pair payZT payST)) payAT)
                                  (Fan (Lift (KT (reify tagAp1)))
                                       (Fan (Fan (Lift (KT tagCode_recFunc))
                                                 (Fan (Lift (Comp Fst Snd))
                                                      (Lift (Comp Fst (Comp Snd Snd)))
                                                      Pair)
                                                 Pair)
                                            (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                            Pair)
                                       Pair)
                                  -- recB: Pair K_a1 (Pair (Pair K_rT (Pair payZT payST)) payBT)
                                  (Fan (Lift (KT (reify tagAp1)))
                                       (Fan (Fan (Lift (KT tagCode_recFunc))
                                                 (Fan (Lift (Comp Fst Snd))
                                                      (Lift (Comp Fst (Comp Snd Snd)))
                                                      Pair)
                                                 Pair)
                                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                            Pair)
                                       Pair)
                                  Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      Pair
  -- axRecPLf s p : LHS = ap2 (RecP s) p O , RHS = O .
  --   payT depth 2: Pair payST payPT.
  --   reify(LHS) = Pair K_a2 (Pair (Pair K_recPTag payST) (Pair payPT O))   -- code O = lf
  --   reify(RHS) = O (= reify (code O) = reify lf)
  body_axRecPLf    : Fun2
  body_axRecPLf    =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Fan (Lift (KT tagCode_recPFunc))
                     (Lift (Comp Fst Snd))
                     Pair)
                (Fan (Lift (Comp Snd Snd))
                     (Lift (KT O))
                     Pair)
                Pair)
           Pair)
      (Lift (KT O))
      Pair
  -- axRecPNd s p a b :
  --   LHS = ap2 (RecP s) p (ap2 Pair a b)
  --   RHS = ap2 s (ap2 Pair p (ap2 Pair a b))
  --                (ap2 Pair (ap2 (RecP s) p a) (ap2 (RecP s) p b))
  --   payT depth 4: Pair payST (Pair payPT (Pair payAT payBT)).
  body_axRecPNd    : Fun2
  body_axRecPNd    =
    Fan
      -- LHS-build
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Fan (Lift (KT tagCode_recPFunc))
                     (Lift (Comp Fst Snd))
                     Pair)
                (Fan (Lift (Comp Fst (Comp Snd Snd)))
                     (Fan (Lift (KT (reify tagAp2)))
                          (Fan (Lift (KT (reify (codeF2 Pair))))
                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    Pair)
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      -- RHS-build
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst Snd))
                (Fan
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                   (Fan (Lift (KT (reify tagAp2)))
                                        (Fan (Lift (KT (reify (codeF2 Pair))))
                                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                  Pair)
                                             Pair)
                                        Pair)
                                   Pair)
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan
                                  (Fan (Lift (KT (reify tagAp2)))
                                       (Fan (Fan (Lift (KT tagCode_recPFunc))
                                                 (Lift (Comp Fst Snd))
                                                 Pair)
                                            (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                 Pair)
                                            Pair)
                                       Pair)
                                  (Fan (Lift (KT (reify tagAp2)))
                                       (Fan (Fan (Lift (KT tagCode_recPFunc))
                                                 (Lift (Comp Fst Snd))
                                                 Pair)
                                            (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                 Pair)
                                            Pair)
                                       Pair)
                                  Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      Pair
  -- axIfLfL a b : LHS = ap2 IfLf O (ap2 Pair a b) , RHS = a .
  --   payT depth 2: Pair payAT payBT.
  --   reify(LHS) = Pair K_a2 (Pair (reify (codeF2 IfLf))
  --                  (Pair O                                        -- code O = lf
  --                        (Pair K_a2 (Pair (reify (codeF2 Pair)) payT))))
  --   reify(RHS) = payAT (= Fst payT)
  body_axIfLfL     : Fun2
  body_axIfLfL     =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 IfLf))))
                (Fan (Lift (KT O))
                     (Fan (Lift (KT (reify tagAp2)))
                          (Fan (Lift (KT (reify (codeF2 Pair))))
                               (Lift Snd)
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      (Lift (Comp Fst Snd))
      Pair
  -- axIfLfN x y a b : LHS = ap2 IfLf (ap2 Pair x y) (ap2 Pair a b) , RHS = b .
  --   payT depth 4: Pair payX (Pair payY (Pair payAT payBT)).
  body_axIfLfN     : Fun2
  body_axIfLfN     =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 IfLf))))
                (Fan
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd Snd)))
                                   Pair)
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                   Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
      Pair
  -- axTreeEqLL takes no args; output is the closed constant
  --   reify (codeFormula (atomic (eqn (ap2 TreeEq O O) O))).
  body_axTreeEqLL  : Fun2
  body_axTreeEqLL  = Lift (KT (reify outAxTreeEqLL))
  -- axTreeEqLN a b : LHS = ap2 TreeEq O (ap2 Pair a b) , RHS = ap2 Pair O O .
  --   payT depth 2: Pair payAT payBT.
  --   RHS is a closed Term whose code reifies to the constant
  --     reify (code (ap2 Pair O O)) = Pair K_a2 (Pair K_pair (Pair O O))
  --   (post-redesign: inner code O = lf, so reify shrinks.)
  body_axTreeEqLN  : Fun2
  body_axTreeEqLN  =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 TreeEq))))
                (Fan (Lift (KT O))
                     (Fan (Lift (KT (reify tagAp2)))
                          (Fan (Lift (KT (reify (codeF2 Pair))))
                               (Lift Snd)
                               Pair)
                          Pair)
                     Pair)
                Pair)
           Pair)
      (Lift (KT (reify (code (ap2 Pair O O)))))
      Pair
  -- axTreeEqNL a b : LHS = ap2 TreeEq (ap2 Pair a b) O , RHS = ap2 Pair O O .
  --   payT depth 2: Pair payAT payBT.
  body_axTreeEqNL  : Fun2
  body_axTreeEqNL  =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 TreeEq))))
                (Fan (Fan (Lift (KT (reify tagAp2)))
                          (Fan (Lift (KT (reify (codeF2 Pair))))
                               (Lift Snd)
                               Pair)
                          Pair)
                     (Lift (KT O))
                     Pair)
                Pair)
           Pair)
      (Lift (KT (reify (code (ap2 Pair O O)))))
      Pair
  -- axTreeEqNN a1 a2 b1 b2 :
  --   LHS = ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2)
  --   RHS = ap2 IfLf (ap2 TreeEq a1 b1)
  --                  (ap2 Pair (ap2 TreeEq a2 b2) (ap2 Pair O O))
  --   payT depth 4: Pair payA1 (Pair payA2 (Pair payB1 payB2)).
  body_axTreeEqNN  : Fun2
  body_axTreeEqNN  =
    Fan
      -- LHS-build:
      --   Pair K_a2 (Pair K_te (Pair (Pair K_a2 (Pair K_pair (Pair payA1 payA2)))
      --                               (Pair K_a2 (Pair K_pair (Pair payB1 payB2)))))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 TreeEq))))
                (Fan
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd Snd)))
                                   Pair)
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                   Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      -- RHS-build:
      --   Pair K_a2 (Pair K_ifLf
      --     (Pair (Pair K_a2 (Pair K_te (Pair payA1 payB1)))
      --           (Pair K_a2 (Pair K_pair
      --             (Pair (Pair K_a2 (Pair K_te (Pair payA2 payB2)))
      --                   (Pair K_a2 (Pair K_pair (Pair K_oo K_oo))))))))
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 IfLf))))
                (Fan
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 TreeEq))))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                   Pair)
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan
                                  (Fan (Lift (KT (reify tagAp2)))
                                       (Fan (Lift (KT (reify (codeF2 TreeEq))))
                                            (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                 Pair)
                                            Pair)
                                       Pair)
                                  (Fan (Lift (KT (reify tagAp2)))
                                       (Fan (Lift (KT (reify (codeF2 Pair))))
                                            (Fan (Lift (KT O))
                                                 (Lift (KT O))
                                                 Pair)
                                            Pair)
                                       Pair)
                                  Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      Pair
  -- axGoodstein a b :
  --   LHS = ap2 IfLf (ap2 TreeEq a b) (ap2 Pair a O) ,
  --   RHS = ap2 IfLf (ap2 TreeEq a b) (ap2 Pair b O) .
  --   payT depth 2: Pair payAT payBT.
  --   The two sides differ only in one position (payAT vs payBT).
  body_axGoodstein : Fun2
  body_axGoodstein =
    Fan
      -- LHS-build:
      --   Pair K_a2 (Pair K_ifLf
      --     (Pair (Pair K_a2 (Pair K_te payT))
      --           (Pair K_a2 (Pair K_pair (Pair payAT O)))))   -- code O = lf
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 IfLf))))
                (Fan
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 TreeEq))))
                              (Lift Snd)
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (KT O))
                                   Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      -- RHS-build: same shape as LHS, only payAT replaced by payBT.
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 IfLf))))
                (Fan
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 TreeEq))))
                              (Lift Snd)
                              Pair)
                         Pair)
                    (Fan (Lift (KT (reify tagAp2)))
                         (Fan (Lift (KT (reify (codeF2 Pair))))
                              (Fan (Lift (Comp Snd Snd))
                                   (Lift (KT O))
                                   Pair)
                              Pair)
                         Pair)
                    Pair)
                Pair)
           Pair)
      Pair
  -- axRefl t : conclusion = atomic (eqn t t).
  --   payT = code t reified.
  --   reify(out) = Pair payT payT.
  body_axRefl      : Fun2
  body_axRefl      = Fan (Lift Snd) (Lift Snd) Pair
  -- axEqTrans a b c : conclusion =
  --   (atomic (eqn a b)) imp ((atomic (eqn a c)) imp (atomic (eqn b c)))
  --   payT depth 3: Pair payAT (Pair payBT payCT).
  body_axEqTrans   : Fun2
  body_axEqTrans   =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Fan (Lift (Comp Fst Snd))
                  (Lift (Comp Fst (Comp Snd Snd)))
                  Pair)
             (Fan (Lift (KT (reify tagImp)))
                  (Fan (Fan (Lift (Comp Fst Snd))
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axEqCong1 f a b : conclusion =
  --   (atomic (eqn a b)) imp (atomic (eqn (ap1 f a) (ap1 f b)))
  --   payT depth 3: Pair payFT (Pair payAT payBT).
  body_axEqCong1   : Fun2
  body_axEqCong1   =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                  (Lift (Comp Snd (Comp Snd Snd)))
                  Pair)
             (Fan (Fan (Lift (KT (reify tagAp1)))
                       (Fan (Lift (Comp Fst Snd))
                            (Lift (Comp Fst (Comp Snd Snd)))
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp1)))
                       (Fan (Lift (Comp Fst Snd))
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axEqCongL g a b c : conclusion =
  --   (atomic (eqn a b)) imp (atomic (eqn (ap2 g a c) (ap2 g b c)))
  --   payT depth 4: Pair payGT (Pair payAT (Pair payBT payCT)).
  body_axEqCongL   : Fun2
  body_axEqCongL   =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                  Pair)
             (Fan (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 Pair)
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axEqCongR g a b c : conclusion =
  --   (atomic (eqn a b)) imp (atomic (eqn (ap2 g c a) (ap2 g c b)))
  --   payT depth 4: Pair payGT (Pair payAT (Pair payBT payCT)).
  --   (Same encoding as axEqCongL; only the inner ap2's argument order
  --    differs in the conclusion: payCT before payAT/payBT.)
  body_axEqCongR   : Fun2
  body_axEqCongR   =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                  Pair)
             (Fan (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Fst (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       Pair)
                  (Fan (Lift (KT (reify tagAp2)))
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axK P Q : conclusion = P imp (Q imp P).
  --   payT depth 2: Pair payP payQ.
  body_axK         : Fun2
  body_axK         =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Lift (Comp Fst Snd))
             (Fan (Lift (KT (reify tagImp)))
                  (Fan (Lift (Comp Snd Snd))
                       (Lift (Comp Fst Snd))
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axS P Q R : conclusion = (P imp (Q imp R)) imp ((P imp Q) imp (P imp R)).
  --   payT depth 3: Pair payP (Pair payQ payR).
  body_axS         : Fun2
  body_axS         =
    Fan (Lift (KT (reify tagImp)))
        (Fan
            -- A = P imp (Q imp R)
            (Fan (Lift (KT (reify tagImp)))
                 (Fan (Lift (Comp Fst Snd))
                      (Fan (Lift (KT (reify tagImp)))
                           (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                (Lift (Comp Snd (Comp Snd Snd)))
                                Pair)
                           Pair)
                      Pair)
                 Pair)
            -- B = (P imp Q) imp (P imp R)
            (Fan (Lift (KT (reify tagImp)))
                 (Fan (Fan (Lift (KT (reify tagImp)))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd)))
                                Pair)
                           Pair)
                      (Fan (Lift (KT (reify tagImp)))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Snd (Comp Snd Snd)))
                                Pair)
                           Pair)
                      Pair)
                 Pair)
            Pair)
        Pair
  -- axNeg P Q : conclusion = (not P) imp ((not Q) imp (Q imp P)).
  --   payT depth 2: Pair payP payQ.
  body_axNeg       : Fun2
  body_axNeg       =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Fan (Lift (KT (reify tagNeg)))
                  (Lift (Comp Fst Snd))
                  Pair)
             (Fan (Lift (KT (reify tagImp)))
                  (Fan (Fan (Lift (KT (reify tagNeg)))
                            (Lift (Comp Snd Snd))
                            Pair)
                       (Fan (Lift (KT (reify tagImp)))
                            (Fan (Lift (Comp Snd Snd))
                                 (Lift (Comp Fst Snd))
                                 Pair)
                            Pair)
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axExFalso P Q : conclusion = P imp ((not P) imp Q).
  --   payT depth 2: Pair payP payQ.
  body_axExFalso   : Fun2
  body_axExFalso   =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Lift (Comp Fst Snd))
             (Fan (Lift (KT (reify tagImp)))
                  (Fan (Fan (Lift (KT (reify tagNeg)))
                            (Lift (Comp Fst Snd))
                            Pair)
                       (Lift (Comp Snd Snd))
                       Pair)
                  Pair)
             Pair)
        Pair
  -- axContrapos P Q : conclusion = (P imp Q) imp ((not Q) imp (not P)).
  --   payT depth 2: Pair payP payQ.
  body_axContrapos : Fun2
  body_axContrapos =
    Fan (Lift (KT (reify tagImp)))
        (Fan (Fan (Lift (KT (reify tagImp)))
                  (Fan (Lift (Comp Fst Snd))
                       (Lift (Comp Snd Snd))
                       Pair)
                  Pair)
             (Fan (Lift (KT (reify tagImp)))
                  (Fan (Fan (Lift (KT (reify tagNeg)))
                            (Lift (Comp Snd Snd))
                            Pair)
                       (Fan (Lift (KT (reify tagNeg)))
                            (Lift (Comp Fst Snd))
                            Pair)
                       Pair)
                  Pair)
             Pair)
        Pair

  -- Recursive primitives.  Encoding shape decides Snd-extraction depth.
  --   ruleSym   : 1 sub-proof at top of payload.       body = Snd b
  --   mp        : (y1, y2) at top of payload.          body = Fst (Snd b)
  --   ruleTrans : (y1, y2) at top of payload.          body = Fst (Snd b)
  --   cong1     : (codeF1 f, y_h) at top of payload.   body = Snd (Snd b)
  --   congL     : (codeF2 g, code x, y_h).             body = Snd (Snd (Snd b))
  --   congR     : (codeF2 g, code x, y_h).             body = Snd (Snd (Snd b))
  --   ruleInst  : (codeVarX, code t, y_h).             body = Snd (Snd (Snd b))
  --   ruleIndBT : (codeP, codev1, codev2, y_b, y_s).   body = Fst (Snd^5 b)
  --
  -- All Snd-of-b extractions encoded as  Post Snd^k Pair  applied at  b .

  -- ruleSym y_h : RECURSIVE.  Given IH thmT(y_h) = code(eqn t u)
  -- (Pair payTcoded payUcoded), produce code(eqn u t) (Pair payUcoded
  -- payTcoded).  The swap is a Fun2-level transposition of Snd b's
  -- two components: Snd(Snd b) and Fst(Snd b).
  body_ruleSym     : Fun2
  body_ruleSym     = Fan (Post (Comp Snd (Comp Snd Snd)) Pair)
                         (Post (Comp Fst (Comp Snd Snd)) Pair)
                         Pair
  -- ruleTrans y1 y2: output is reify(codeFormula (atomic (eqn t v))) =
  -- Pair payT_r payV_r.  After distribution Snd b = Pair (thmT y1_r)
  -- (thmT y2_r) , the body extracts payT_r = Fst(thmT y1_r) and
  -- payV_r = Snd(thmT y2_r) and pairs them.  Body uses the
  -- postSndBody_eval (Comp Fst Fst / Comp Snd Snd) helpers internally.
  body_ruleTrans   : Fun2
  body_ruleTrans   =
    Fan (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair)
        (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
        Pair
  -- cong1 f y_h: output is reify(codeFormula(atomic (eqn (ap1 f t) (ap1 f u)))) =
  -- Pair (Pair K_a1 (Pair payF payT_r)) (Pair K_a1 (Pair payF payU_r)) where
  --   K_a1 = reify tagAp1, payF = reify(codeF1 f),
  --   payT_r = reify(code t), payU_r = reify(code u).
  -- After distribution Snd b = Pair (thmT payF) (thmT y_h_r) and IH on
  -- y_h_r = Pair payT_r payU_r:
  --   payF       = Fst(Snd a)               (from a directly; no distrib)
  --   payT_r     = Fst(Snd(Snd b))          (Fst of thmT y_h_r)
  --   payU_r     = Snd(Snd(Snd b))          (Snd of thmT y_h_r)
  body_cong1       : Fun2
  body_cong1       =
    Fan
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (Comp Fst Snd))
                (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                Pair)
           Pair)
      (Fan (Lift (KT (reify tagAp1)))
           (Fan (Lift (Comp Fst Snd))
                (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                Pair)
           Pair)
      Pair
  -- congL g x y_h: output is reify(codeFormula(atomic(eqn (ap2 g t x) (ap2 g u x)))).
  -- After two-level distribution Snd b = Pair (thmT payG) (Pair (thmT y_h_r) (thmT payX))
  -- and IH on y_h_r = Pair payT_r payU_r:
  --   K_a2  = constant
  --   payG  = Fst(Snd a)
  --   payT_r = Fst(Fst(Snd(Snd b)))     (Fst of thmT y_h_r)
  --   payU_r = Snd(Fst(Snd(Snd b)))     (Snd of thmT y_h_r)
  --   payX  = Snd(Snd(Snd a))
  body_congL       : Fun2
  body_congL       =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                     (Lift (Comp Snd (Comp Snd Snd)))
                     Pair)
                Pair)
           Pair)
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                     (Lift (Comp Snd (Comp Snd Snd)))
                     Pair)
                Pair)
           Pair)
      Pair
  -- congR g x y_h: similar to congL but the output's inner Pair has
  -- payX BEFORE payT_r/payU_r:
  --   reify(outCongR g x t u) =
  --     Pair (Pair K_a2 (Pair payG (Pair payX payT_r)))
  --          (Pair K_a2 (Pair payG (Pair payX payU_r)))
  -- Body has the same structure as body_congL with the inner-pair
  -- arguments swapped.
  body_congR       : Fun2
  body_congR       =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Lift (Comp Snd (Comp Snd Snd)))
                     (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                     Pair)
                Pair)
           Pair)
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (Comp Fst Snd))
                (Fan (Lift (Comp Snd (Comp Snd Snd)))
                     (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                     Pair)
                Pair)
           Pair)
      Pair
  -- mp y1 y2: output is reify(codeFormula Q).  After distribution
  -- Snd b = Pair (thmT y1_r) (thmT y2_r) , and IH1 says
  -- thmT y1_r = reify(codeFormula (P imp Q)) = Pair K_imp (Pair pT qT).
  -- The body extracts qT = Snd(Snd(Fst(Snd b))) using
  -- postSndBody_eval (Comp Snd (Comp Snd Fst)).
  body_mp          : Fun2
  body_mp          = Post (Comp (Comp Snd (Comp Snd Fst)) (Comp Snd Snd)) Pair
  -- ruleInst x t y_h: output is reify(codeFormula(substF x t P)).
  -- The body computes  subT(<payVarX, payT>, codeFormulaP)  via the
  -- subT combinator from BRA.SubT (which lifts codedSubst to terms).
  --   payVarX = reify(code(var x))     = Fst(Snd a)
  --   payT    = reify(code t)           = Snd(Snd(Snd a))
  --   codeFormulaP = reify(codeFormula P) = Fst(Snd(Snd b))   (Snd of distH)
  -- body = Fan ARGS_extractor CODEP_extractor subT  so that
  --   ap2 body a b = ap2 subT (ARGS_extractor a b) (CODEP_extractor a b) .
  body_ruleInst    : Fun2
  body_ruleInst    =
    Fan
      (Fan (Lift (Comp Fst Snd))
           (Lift (Comp Snd (Comp Snd Snd)))
           Pair)
      (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
      subT
  -- ruleIndBT: output is reify (codeFormula P), and codeFormula P sits
  -- at Fst(Snd a) since the encoding is
  --   nd tagRuleIndBT (nd (codeFormula P) (...)) .
  -- Body extracts Fst(Snd a) directly; no IH application needed.
  body_ruleIndBT   : Fun2
  body_ruleIndBT   = Lift (Comp Fst Snd)

  -- 4 safe-default-axiom bodies.  axFstLf, axSndLf, axIfLfLL have closed
  -- output (no parameters in the conclusion); body returns the closed
  -- encoded out via Lift (KT _).  axIfLfNL takes (x, y) parameters; its
  -- body extracts payX/payY from payload and builds the encoded LHS.

  body_axFstLf     : Fun2
  body_axFstLf     = Lift (KT (reify outAxFstLf))

  body_axSndLf     : Fun2
  body_axSndLf     = Lift (KT (reify outAxSndLf))

  body_axIfLfLL    : Fun2
  body_axIfLfLL    = Lift (KT (reify outAxIfLfLL))

  -- axIfLfNL x y : LHS = ap2 IfLf (ap2 Pair x y) O , RHS = O .
  --   payT = Pair payX payY.  Extract payT directly via Lift Snd (no need to split).
  --   reify(LHS) = Pair K_a2 (Pair (reify (codeF2 IfLf))
  --                  (Pair (Pair K_a2 (Pair (reify (codeF2 Pair)) payT)) O))
  --   reify(RHS) = O.
  body_axIfLfNL    : Fun2
  body_axIfLfNL    =
    Fan
      (Fan (Lift (KT (reify tagAp2)))
           (Fan (Lift (KT (reify (codeF2 IfLf))))
                (Fan (Fan (Lift (KT (reify tagAp2)))
                          (Fan (Lift (KT (reify (codeF2 Pair))))
                               (Lift Snd)
                               Pair)
                          Pair)
                     (Lift (KT O))
                     Pair)
                Pair)
           Pair)
      (Lift (KT O))
      Pair

  -- body_ruleInst2 : analog of body_ruleInst with TWO (var, term) pairs.
  -- Payload structure (from encRuleInst2 in BRA.Thm.Parts.RuleInst2):
  --   a = Pair tag (Pair xACode (Pair xBCode (Pair y_h_r (Pair tACode tBCode))))
  -- Extractors over a:
  --   payVarA = Fst(Snd a)                                    -- xACode
  --   payVarB = Fst(Snd(Snd a))                                -- xBCode
  --   payTA   = Fst(Snd(Snd(Snd(Snd a))))                      -- tACode
  --   payTB   = Snd(Snd(Snd(Snd(Snd a))))                      -- tBCode
  -- The args term subT2 expects is
  --   Pair (Pair payVarA payTA) (Pair payVarB payTB) .
  -- The codeFP comes from b: thmT(y_h_r) sits at Fst(Snd(Snd(Snd b)))
  -- in the rec result; via Post the extractor is
  --   Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd)) over (Pair a b).
  body_ruleInst2   : Fun2
  body_ruleInst2   =
    Fan
      (Fan
        (Fan (Lift (Comp Fst Snd))
             (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
             Pair)
        (Fan (Lift (Comp Fst (Comp Snd Snd)))
             (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
             Pair)
        Pair)
      (Post (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair)
      subT2

  ------------------------------------------------------------------
  -- 40 checkTagN combinators.

  checkTag_axI         : Fun2
  checkTag_axI         = Fan (Lift (KT tagCode_axI)) (Lift Fst) TreeEq
  checkTag_axFst       : Fun2
  checkTag_axFst       = Fan (Lift (KT tagCode_axFst)) (Lift Fst) TreeEq
  checkTag_axSnd       : Fun2
  checkTag_axSnd       = Fan (Lift (KT tagCode_axSnd)) (Lift Fst) TreeEq
  checkTag_axConst     : Fun2
  checkTag_axConst     = Fan (Lift (KT tagCode_axConst)) (Lift Fst) TreeEq
  checkTag_axComp      : Fun2
  checkTag_axComp      = Fan (Lift (KT tagCode_axComp)) (Lift Fst) TreeEq
  checkTag_axComp2     : Fun2
  checkTag_axComp2     = Fan (Lift (KT tagCode_axComp2)) (Lift Fst) TreeEq
  checkTag_axLift      : Fun2
  checkTag_axLift      = Fan (Lift (KT tagCode_axLift)) (Lift Fst) TreeEq
  checkTag_axPost      : Fun2
  checkTag_axPost      = Fan (Lift (KT tagCode_axPost)) (Lift Fst) TreeEq
  checkTag_axFan       : Fun2
  checkTag_axFan       = Fan (Lift (KT tagCode_axFan)) (Lift Fst) TreeEq
  checkTag_axKT        : Fun2
  checkTag_axKT        = Fan (Lift (KT tagCode_axKT)) (Lift Fst) TreeEq
  checkTag_axRecLf     : Fun2
  checkTag_axRecLf     = Fan (Lift (KT tagCode_axRecLf)) (Lift Fst) TreeEq
  checkTag_axRecNd     : Fun2
  checkTag_axRecNd     = Fan (Lift (KT tagCode_axRecNd)) (Lift Fst) TreeEq
  checkTag_axRecPLf    : Fun2
  checkTag_axRecPLf    = Fan (Lift (KT tagCode_axRecPLf)) (Lift Fst) TreeEq
  checkTag_axRecPNd    : Fun2
  checkTag_axRecPNd    = Fan (Lift (KT tagCode_axRecPNd)) (Lift Fst) TreeEq
  checkTag_axIfLfL     : Fun2
  checkTag_axIfLfL     = Fan (Lift (KT tagCode_axIfLfL)) (Lift Fst) TreeEq
  checkTag_axIfLfN     : Fun2
  checkTag_axIfLfN     = Fan (Lift (KT tagCode_axIfLfN)) (Lift Fst) TreeEq
  checkTag_axTreeEqLL  : Fun2
  checkTag_axTreeEqLL  = Fan (Lift (KT tagCode_axTreeEqLL)) (Lift Fst) TreeEq
  checkTag_axTreeEqLN  : Fun2
  checkTag_axTreeEqLN  = Fan (Lift (KT tagCode_axTreeEqLN)) (Lift Fst) TreeEq
  checkTag_axTreeEqNL  : Fun2
  checkTag_axTreeEqNL  = Fan (Lift (KT tagCode_axTreeEqNL)) (Lift Fst) TreeEq
  checkTag_axTreeEqNN  : Fun2
  checkTag_axTreeEqNN  = Fan (Lift (KT tagCode_axTreeEqNN)) (Lift Fst) TreeEq
  checkTag_axGoodstein : Fun2
  checkTag_axGoodstein = Fan (Lift (KT tagCode_axGoodstein)) (Lift Fst) TreeEq
  checkTag_axRefl      : Fun2
  checkTag_axRefl      = Fan (Lift (KT tagCode_axRefl)) (Lift Fst) TreeEq
  checkTag_ruleSym     : Fun2
  checkTag_ruleSym     = Fan (Lift (KT tagCode_ruleSym)) (Lift Fst) TreeEq
  checkTag_ruleTrans   : Fun2
  checkTag_ruleTrans   = Fan (Lift (KT tagCode_ruleTrans)) (Lift Fst) TreeEq
  checkTag_cong1       : Fun2
  checkTag_cong1       = Fan (Lift (KT tagCode_cong1)) (Lift Fst) TreeEq
  checkTag_congL       : Fun2
  checkTag_congL       = Fan (Lift (KT tagCode_congL)) (Lift Fst) TreeEq
  checkTag_congR       : Fun2
  checkTag_congR       = Fan (Lift (KT tagCode_congR)) (Lift Fst) TreeEq
  checkTag_axEqTrans   : Fun2
  checkTag_axEqTrans   = Fan (Lift (KT tagCode_axEqTrans)) (Lift Fst) TreeEq
  checkTag_axEqCong1   : Fun2
  checkTag_axEqCong1   = Fan (Lift (KT tagCode_axEqCong1)) (Lift Fst) TreeEq
  checkTag_axEqCongL   : Fun2
  checkTag_axEqCongL   = Fan (Lift (KT tagCode_axEqCongL)) (Lift Fst) TreeEq
  checkTag_axEqCongR   : Fun2
  checkTag_axEqCongR   = Fan (Lift (KT tagCode_axEqCongR)) (Lift Fst) TreeEq
  checkTag_axK         : Fun2
  checkTag_axK         = Fan (Lift (KT tagCode_axK)) (Lift Fst) TreeEq
  checkTag_axS         : Fun2
  checkTag_axS         = Fan (Lift (KT tagCode_axS)) (Lift Fst) TreeEq
  checkTag_axNeg       : Fun2
  checkTag_axNeg       = Fan (Lift (KT tagCode_axNeg)) (Lift Fst) TreeEq
  checkTag_axExFalso   : Fun2
  checkTag_axExFalso   = Fan (Lift (KT tagCode_axExFalso)) (Lift Fst) TreeEq
  checkTag_axContrapos : Fun2
  checkTag_axContrapos = Fan (Lift (KT tagCode_axContrapos)) (Lift Fst) TreeEq
  checkTag_mp          : Fun2
  checkTag_mp          = Fan (Lift (KT tagCode_mp)) (Lift Fst) TreeEq
  checkTag_ruleInst    : Fun2
  checkTag_ruleInst    = Fan (Lift (KT tagCode_ruleInst)) (Lift Fst) TreeEq
  checkTag_ruleIndBT   : Fun2
  checkTag_ruleIndBT   = Fan (Lift (KT tagCode_ruleIndBT)) (Lift Fst) TreeEq

  -- 4 safe-default checkTags.
  checkTag_axFstLf     : Fun2
  checkTag_axFstLf     = Fan (Lift (KT tagCode_axFstLf)) (Lift Fst) TreeEq
  checkTag_axSndLf     : Fun2
  checkTag_axSndLf     = Fan (Lift (KT tagCode_axSndLf)) (Lift Fst) TreeEq
  checkTag_axIfLfLL    : Fun2
  checkTag_axIfLfLL    = Fan (Lift (KT tagCode_axIfLfLL)) (Lift Fst) TreeEq
  checkTag_axIfLfNL    : Fun2
  checkTag_axIfLfNL    = Fan (Lift (KT tagCode_axIfLfNL)) (Lift Fst) TreeEq
  checkTag_ruleInst2   : Fun2
  checkTag_ruleInst2   = Fan (Lift (KT tagCode_ruleInst2)) (Lift Fst) TreeEq

  ------------------------------------------------------------------
  -- 44 branch + 43 next combinators (build cascade bottom-up).
  --
  -- Cascade EXTENDED by the 4 safe-default axioms after ruleIndBT and
  -- the simultaneous double-substitution tag (tagRuleInst2) after axIfLfNL:
  --   branch_ruleIndBT chains to next_ruleIndBT (-> checkTag_axFstLf).
  --   branch_axIfLfNL chains to next_axIfLfNL (-> checkTag_ruleInst2).
  --   The chain ends at branch_ruleInst2 = Fan body_ruleInst2 fbBody Pair.

  branch_ruleInst2   : Fun2
  branch_ruleInst2   = Fan body_ruleInst2   fbBody             Pair
  next_axIfLfNL      : Fun2
  next_axIfLfNL      = Fan checkTag_ruleInst2   branch_ruleInst2   IfLf
  branch_axIfLfNL    : Fun2
  branch_axIfLfNL    = Fan body_axIfLfNL    next_axIfLfNL      Pair
  next_axIfLfLL      : Fun2
  next_axIfLfLL      = Fan checkTag_axIfLfNL    branch_axIfLfNL    IfLf
  branch_axIfLfLL    : Fun2
  branch_axIfLfLL    = Fan body_axIfLfLL    next_axIfLfLL      Pair
  next_axSndLf       : Fun2
  next_axSndLf       = Fan checkTag_axIfLfLL    branch_axIfLfLL    IfLf
  branch_axSndLf     : Fun2
  branch_axSndLf     = Fan body_axSndLf     next_axSndLf       Pair
  next_axFstLf       : Fun2
  next_axFstLf       = Fan checkTag_axSndLf     branch_axSndLf     IfLf
  branch_axFstLf     : Fun2
  branch_axFstLf     = Fan body_axFstLf     next_axFstLf       Pair
  next_ruleIndBT     : Fun2
  next_ruleIndBT     = Fan checkTag_axFstLf     branch_axFstLf     IfLf

  branch_ruleIndBT   : Fun2
  branch_ruleIndBT   = Fan body_ruleIndBT   next_ruleIndBT     Pair
  next_ruleInst      : Fun2
  next_ruleInst      = Fan checkTag_ruleIndBT   branch_ruleIndBT   IfLf
  branch_ruleInst    : Fun2
  branch_ruleInst    = Fan body_ruleInst    next_ruleInst      Pair
  next_mp            : Fun2
  next_mp            = Fan checkTag_ruleInst    branch_ruleInst    IfLf
  branch_mp          : Fun2
  branch_mp          = Fan body_mp          next_mp            Pair
  next_axContrapos   : Fun2
  next_axContrapos   = Fan checkTag_mp          branch_mp          IfLf
  branch_axContrapos : Fun2
  branch_axContrapos = Fan body_axContrapos next_axContrapos   Pair
  next_axExFalso     : Fun2
  next_axExFalso     = Fan checkTag_axContrapos branch_axContrapos IfLf
  branch_axExFalso   : Fun2
  branch_axExFalso   = Fan body_axExFalso   next_axExFalso     Pair
  next_axNeg         : Fun2
  next_axNeg         = Fan checkTag_axExFalso   branch_axExFalso   IfLf
  branch_axNeg       : Fun2
  branch_axNeg       = Fan body_axNeg       next_axNeg         Pair
  next_axS           : Fun2
  next_axS           = Fan checkTag_axNeg       branch_axNeg       IfLf
  branch_axS         : Fun2
  branch_axS         = Fan body_axS         next_axS           Pair
  next_axK           : Fun2
  next_axK           = Fan checkTag_axS         branch_axS         IfLf
  branch_axK         : Fun2
  branch_axK         = Fan body_axK         next_axK           Pair
  next_axEqCongR     : Fun2
  next_axEqCongR     = Fan checkTag_axK         branch_axK         IfLf
  branch_axEqCongR   : Fun2
  branch_axEqCongR   = Fan body_axEqCongR   next_axEqCongR     Pair
  next_axEqCongL     : Fun2
  next_axEqCongL     = Fan checkTag_axEqCongR   branch_axEqCongR   IfLf
  branch_axEqCongL   : Fun2
  branch_axEqCongL   = Fan body_axEqCongL   next_axEqCongL     Pair
  next_axEqCong1     : Fun2
  next_axEqCong1     = Fan checkTag_axEqCongL   branch_axEqCongL   IfLf
  branch_axEqCong1   : Fun2
  branch_axEqCong1   = Fan body_axEqCong1   next_axEqCong1     Pair
  next_axEqTrans     : Fun2
  next_axEqTrans     = Fan checkTag_axEqCong1   branch_axEqCong1   IfLf
  branch_axEqTrans   : Fun2
  branch_axEqTrans   = Fan body_axEqTrans   next_axEqTrans     Pair
  next_congR         : Fun2
  next_congR         = Fan checkTag_axEqTrans   branch_axEqTrans   IfLf
  branch_congR       : Fun2
  branch_congR       = Fan body_congR       next_congR         Pair
  next_congL         : Fun2
  next_congL         = Fan checkTag_congR       branch_congR       IfLf
  branch_congL       : Fun2
  branch_congL       = Fan body_congL       next_congL         Pair
  next_cong1         : Fun2
  next_cong1         = Fan checkTag_congL       branch_congL       IfLf
  branch_cong1       : Fun2
  branch_cong1       = Fan body_cong1       next_cong1         Pair
  next_ruleTrans     : Fun2
  next_ruleTrans     = Fan checkTag_cong1       branch_cong1       IfLf
  branch_ruleTrans   : Fun2
  branch_ruleTrans   = Fan body_ruleTrans   next_ruleTrans     Pair
  next_ruleSym       : Fun2
  next_ruleSym       = Fan checkTag_ruleTrans   branch_ruleTrans   IfLf
  branch_ruleSym     : Fun2
  branch_ruleSym     = Fan body_ruleSym     next_ruleSym       Pair
  next_axRefl        : Fun2
  next_axRefl        = Fan checkTag_ruleSym     branch_ruleSym     IfLf
  branch_axRefl      : Fun2
  branch_axRefl      = Fan body_axRefl      next_axRefl        Pair
  next_axGoodstein   : Fun2
  next_axGoodstein   = Fan checkTag_axRefl      branch_axRefl      IfLf
  branch_axGoodstein : Fun2
  branch_axGoodstein = Fan body_axGoodstein next_axGoodstein   Pair
  next_axTreeEqNN    : Fun2
  next_axTreeEqNN    = Fan checkTag_axGoodstein branch_axGoodstein IfLf
  branch_axTreeEqNN  : Fun2
  branch_axTreeEqNN  = Fan body_axTreeEqNN  next_axTreeEqNN    Pair
  next_axTreeEqNL    : Fun2
  next_axTreeEqNL    = Fan checkTag_axTreeEqNN  branch_axTreeEqNN  IfLf
  branch_axTreeEqNL  : Fun2
  branch_axTreeEqNL  = Fan body_axTreeEqNL  next_axTreeEqNL    Pair
  next_axTreeEqLN    : Fun2
  next_axTreeEqLN    = Fan checkTag_axTreeEqNL  branch_axTreeEqNL  IfLf
  branch_axTreeEqLN  : Fun2
  branch_axTreeEqLN  = Fan body_axTreeEqLN  next_axTreeEqLN    Pair
  next_axTreeEqLL    : Fun2
  next_axTreeEqLL    = Fan checkTag_axTreeEqLN  branch_axTreeEqLN  IfLf
  branch_axTreeEqLL  : Fun2
  branch_axTreeEqLL  = Fan body_axTreeEqLL  next_axTreeEqLL    Pair
  next_axIfLfN       : Fun2
  next_axIfLfN       = Fan checkTag_axTreeEqLL  branch_axTreeEqLL  IfLf
  branch_axIfLfN     : Fun2
  branch_axIfLfN     = Fan body_axIfLfN     next_axIfLfN       Pair
  next_axIfLfL       : Fun2
  next_axIfLfL       = Fan checkTag_axIfLfN     branch_axIfLfN     IfLf
  branch_axIfLfL     : Fun2
  branch_axIfLfL     = Fan body_axIfLfL     next_axIfLfL       Pair
  next_axRecPNd      : Fun2
  next_axRecPNd      = Fan checkTag_axIfLfL     branch_axIfLfL     IfLf
  branch_axRecPNd    : Fun2
  branch_axRecPNd    = Fan body_axRecPNd    next_axRecPNd      Pair
  next_axRecPLf      : Fun2
  next_axRecPLf      = Fan checkTag_axRecPNd    branch_axRecPNd    IfLf
  branch_axRecPLf    : Fun2
  branch_axRecPLf    = Fan body_axRecPLf    next_axRecPLf      Pair
  next_axRecNd       : Fun2
  next_axRecNd       = Fan checkTag_axRecPLf    branch_axRecPLf    IfLf
  branch_axRecNd     : Fun2
  branch_axRecNd     = Fan body_axRecNd     next_axRecNd       Pair
  next_axRecLf       : Fun2
  next_axRecLf       = Fan checkTag_axRecNd     branch_axRecNd     IfLf
  branch_axRecLf     : Fun2
  branch_axRecLf     = Fan body_axRecLf     next_axRecLf       Pair
  next_axKT          : Fun2
  next_axKT          = Fan checkTag_axRecLf     branch_axRecLf     IfLf
  branch_axKT        : Fun2
  branch_axKT        = Fan body_axZ         next_axKT          Pair
  next_axFan         : Fun2
  next_axFan         = Fan checkTag_axKT        branch_axKT        IfLf
  branch_axFan       : Fun2
  branch_axFan       = Fan body_axFan       next_axFan         Pair
  next_axPost        : Fun2
  next_axPost        = Fan checkTag_axFan       branch_axFan       IfLf
  branch_axPost      : Fun2
  branch_axPost      = Fan body_axPost      next_axPost        Pair
  next_axLift        : Fun2
  next_axLift        = Fan checkTag_axPost      branch_axPost      IfLf
  branch_axLift      : Fun2
  branch_axLift      = Fan body_axLift      next_axLift        Pair
  next_axComp2       : Fun2
  next_axComp2       = Fan checkTag_axLift      branch_axLift      IfLf
  branch_axComp2     : Fun2
  branch_axComp2     = Fan body_axComp2     next_axComp2       Pair
  next_axComp        : Fun2
  next_axComp        = Fan checkTag_axComp2     branch_axComp2     IfLf
  branch_axComp      : Fun2
  branch_axComp      = Fan body_axComp      next_axComp        Pair
  next_axConst       : Fun2
  next_axConst       = Fan checkTag_axComp      branch_axComp      IfLf
  branch_axConst     : Fun2
  branch_axConst     = Fan body_axConst     next_axConst       Pair
  next_axSnd         : Fun2
  next_axSnd         = Fan checkTag_axConst     branch_axConst     IfLf
  branch_axSnd       : Fun2
  branch_axSnd       = Fan body_axSnd       next_axSnd         Pair
  next_axFst         : Fun2
  next_axFst         = Fan checkTag_axSnd       branch_axSnd       IfLf
  branch_axFst       : Fun2
  branch_axFst       = Fan body_axFst       next_axFst         Pair
  next_axI           : Fun2
  next_axI           = Fan checkTag_axFst       branch_axFst       IfLf
  branch_axI         : Fun2
  branch_axI         = Fan body_axI         next_axI           Pair

  ------------------------------------------------------------------
  -- Top-level dispatch and step function.

  dispatch : Fun2
  dispatch = Fan checkTag_axI branch_axI IfLf

  sndProj : Fun2
  sndProj = Post Snd Pair

  discComb : Fun2
  discComb = Lift (Comp Fst Fst)

  branchesTop : Fun2
  branchesTop = Fan dispatch sndProj Pair

  stepProto : Fun2
  stepProto = Fan discComb branchesTop IfLf

  thmT : Fun1
  thmT = Rec O stepProto

  ------------------------------------------------------------------
  -- Structural specs of  thmT  needed by  BRA.Thm11.Thm11 .
  --
  -- Both  thmT  and its tree-level encoding  codeF1 thmT  are closed
  -- (built only from constants and combinator wiring; the  KT-args
  -- inside are  reify <closed Tree> ).  Substitution and codedSubst
  -- are therefore the identity; both reduce to  refl  inside the
  -- abstract block where  thmT  unfolds.

  thClosed : (x : Nat) (r : Term) -> Eq (substF1 x r thmT) thmT
  thClosed x r = refl

  codeF1Th_noVar :
    (x : Nat) (repl : Tree) ->
    Eq (codedSubst repl (code (var x)) (codeF1 thmT)) (codeF1 thmT)
  codeF1Th_noVar x repl = refl

  ------------------------------------------------------------------
  -- TreeEq distinctness on natCode-reified trees (meta-recursive).

  teqEq : (n : Nat) ->
    Deriv (atomic (eqn (ap2 TreeEq (reify (natCode n)) (reify (natCode n))) O))
  teqEq zero    = axTreeEqLL
  teqEq (suc n) =
    let prev : Term
        prev = reify (natCode n)
        e1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O prev) (ap2 Pair O prev))
                                 (ap2 IfLf (ap2 TreeEq O O)
                                           (ap2 Pair (ap2 TreeEq prev prev)
                                                     (ap2 Pair O O)))))
        e1 = axTreeEqNN O prev O prev
        e2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq O O)
                                          (ap2 Pair (ap2 TreeEq prev prev) (ap2 Pair O O)))
                                 (ap2 IfLf O
                                          (ap2 Pair (ap2 TreeEq prev prev) (ap2 Pair O O)))))
        e2 = congL IfLf (ap2 Pair (ap2 TreeEq prev prev) (ap2 Pair O O)) axTreeEqLL
        e3a : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq prev prev) (ap2 Pair O O))
                                  (ap2 Pair O (ap2 Pair O O))))
        e3a = congL Pair (ap2 Pair O O) (teqEq n)
        e3 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 TreeEq prev prev) (ap2 Pair O O)))
                                 (ap2 IfLf O (ap2 Pair O (ap2 Pair O O)))))
        e3 = congR IfLf O e3a
        e4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair O (ap2 Pair O O))) O))
        e4 = axIfLfL O (ap2 Pair O O)
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))

  teqDiff : (n m : Nat) -> Eq (natEq n m) false ->
    Deriv (atomic (eqn (ap2 TreeEq (reify (natCode n)) (reify (natCode m)))
                       (ap2 Pair O O)))
  teqDiff zero    zero    ()
  teqDiff zero    (suc m) _  = axTreeEqLN O (reify (natCode m))
  teqDiff (suc n) zero    _  = axTreeEqNL O (reify (natCode n))
  teqDiff (suc n) (suc m) ne =
    let prev_n : Term
        prev_n = reify (natCode n)
        prev_m : Term
        prev_m = reify (natCode m)
        e1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O prev_n) (ap2 Pair O prev_m))
                                 (ap2 IfLf (ap2 TreeEq O O)
                                           (ap2 Pair (ap2 TreeEq prev_n prev_m)
                                                     (ap2 Pair O O)))))
        e1 = axTreeEqNN O prev_n O prev_m
        e2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq O O)
                                          (ap2 Pair (ap2 TreeEq prev_n prev_m) (ap2 Pair O O)))
                                 (ap2 IfLf O
                                          (ap2 Pair (ap2 TreeEq prev_n prev_m) (ap2 Pair O O)))))
        e2 = congL IfLf (ap2 Pair (ap2 TreeEq prev_n prev_m) (ap2 Pair O O)) axTreeEqLL
        rec : Deriv (atomic (eqn (ap2 TreeEq prev_n prev_m) (ap2 Pair O O)))
        rec = teqDiff n m ne
        e3a : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq prev_n prev_m) (ap2 Pair O O))
                                  (ap2 Pair (ap2 Pair O O) (ap2 Pair O O))))
        e3a = congL Pair (ap2 Pair O O) rec
        e3 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 TreeEq prev_n prev_m) (ap2 Pair O O)))
                                 (ap2 IfLf O (ap2 Pair (ap2 Pair O O) (ap2 Pair O O)))))
        e3 = congR IfLf O e3a
        e4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 Pair O O) (ap2 Pair O O))) (ap2 Pair O O)))
        e4 = axIfLfL (ap2 Pair O O) (ap2 Pair O O)
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))

  ------------------------------------------------------------------
  -- Generic cascade-step lemmas (parameterised over checkTag, body,
  -- and the next Fun2; one definition serves all 40 cascade levels).

  -- Tag-mismatch: checkTag returns Pair O O, IfLf falls through to next.
  cascadeStep : (chk body nx : Fun2) (a b : Term) ->
    Deriv (atomic (eqn (ap2 chk a b) (ap2 Pair O O))) ->
    Deriv (atomic (eqn (ap2 (Fan chk (Fan body nx Pair) IfLf) a b)
                       (ap2 nx a b)))
  cascadeStep chk body nx a b chkFail =
    let e1 : Deriv (atomic (eqn (ap2 (Fan chk (Fan body nx Pair) IfLf) a b)
                                 (ap2 IfLf (ap2 chk a b)
                                           (ap2 (Fan body nx Pair) a b))))
        e1 = axFan chk (Fan body nx Pair) IfLf a b
        e2 : Deriv (atomic (eqn (ap2 (Fan body nx Pair) a b)
                                 (ap2 Pair (ap2 body a b) (ap2 nx a b))))
        e2 = axFan body nx Pair a b
        e3 : Deriv (atomic (eqn (ap2 IfLf (ap2 chk a b) (ap2 (Fan body nx Pair) a b))
                                 (ap2 IfLf (ap2 Pair O O) (ap2 (Fan body nx Pair) a b))))
        e3 = congL IfLf (ap2 (Fan body nx Pair) a b) chkFail
        e4 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair O O) (ap2 (Fan body nx Pair) a b))
                                 (ap2 IfLf (ap2 Pair O O) (ap2 Pair (ap2 body a b) (ap2 nx a b)))))
        e4 = congR IfLf (ap2 Pair O O) e2
        e5 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair O O) (ap2 Pair (ap2 body a b) (ap2 nx a b)))
                                 (ap2 nx a b)))
        e5 = axIfLfN O O (ap2 body a b) (ap2 nx a b)
    in ruleTrans e1 (ruleTrans e3 (ruleTrans e4 e5))

  -- Tag-hit: checkTag returns O, IfLf takes the body branch.
  cascadeHit : (chk body nx : Fun2) (a b : Term) ->
    Deriv (atomic (eqn (ap2 chk a b) O)) ->
    Deriv (atomic (eqn (ap2 (Fan chk (Fan body nx Pair) IfLf) a b)
                       (ap2 body a b)))
  cascadeHit chk body nx a b chkPass =
    let e1 : Deriv (atomic (eqn (ap2 (Fan chk (Fan body nx Pair) IfLf) a b)
                                 (ap2 IfLf (ap2 chk a b)
                                           (ap2 (Fan body nx Pair) a b))))
        e1 = axFan chk (Fan body nx Pair) IfLf a b
        e2 : Deriv (atomic (eqn (ap2 (Fan body nx Pair) a b)
                                 (ap2 Pair (ap2 body a b) (ap2 nx a b))))
        e2 = axFan body nx Pair a b
        e3 : Deriv (atomic (eqn (ap2 IfLf (ap2 chk a b) (ap2 (Fan body nx Pair) a b))
                                 (ap2 IfLf O (ap2 (Fan body nx Pair) a b))))
        e3 = congL IfLf (ap2 (Fan body nx Pair) a b) chkPass
        e4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 (Fan body nx Pair) a b))
                                 (ap2 IfLf O (ap2 Pair (ap2 body a b) (ap2 nx a b)))))
        e4 = congR IfLf O e2
        e5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 body a b) (ap2 nx a b)))
                                 (ap2 body a b)))
        e5 = axIfLfL (ap2 body a b) (ap2 nx a b)
    in ruleTrans e1 (ruleTrans e3 (ruleTrans e4 e5))

  ------------------------------------------------------------------
  -- Top-level helpers (verbatim from BRA.Thm.StepProto).

  sndProj_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 sndProj a b) b))
  sndProj_eval a b =
    let s1 : Deriv (atomic (eqn (ap2 (Post Snd Pair) a b)
                                 (ap1 Snd (ap2 Pair a b))))
        s1 = axPost Snd Pair a b
        s2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
        s2 = axSnd a b
    in ruleTrans s1 s2

  discComb_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 discComb a b) (ap1 Fst (ap1 Fst a))))
  discComb_eval a b =
    let s1 : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Fst)) a b)
                                 (ap1 (Comp Fst Fst) a)))
        s1 = axLift (Comp Fst Fst) a b
        s2 : Deriv (atomic (eqn (ap1 (Comp Fst Fst) a)
                                 (ap1 Fst (ap1 Fst a))))
        s2 = axComp Fst Fst a
    in ruleTrans s1 s2

  -- Top-tag passthrough: Fst(Fst a) = O ==> stepProto a b = dispatch a b.
  stepProto_top : (a b : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) O)) ->
    Deriv (atomic (eqn (ap2 stepProto a b) (ap2 dispatch a b)))
  stepProto_top a b discO =
    let e1 : Deriv (atomic (eqn (ap2 stepProto a b)
                                 (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))))
        e1 = axFan discComb branchesTop IfLf a b
        e2a : Deriv (atomic (eqn (ap2 discComb a b) (ap1 Fst (ap1 Fst a))))
        e2a = discComb_eval a b
        e2 : Deriv (atomic (eqn (ap2 discComb a b) O))
        e2 = ruleTrans e2a discO
        e3a : Deriv (atomic (eqn (ap2 branchesTop a b)
                                  (ap2 Pair (ap2 dispatch a b) (ap2 sndProj a b))))
        e3a = axFan dispatch sndProj Pair a b
        e3 : Deriv (atomic (eqn (ap2 branchesTop a b)
                                 (ap2 Pair (ap2 dispatch a b) b)))
        e3 = ruleTrans e3a (congR Pair (ap2 dispatch a b) (sndProj_eval a b))
        e4 : Deriv (atomic (eqn (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))
                                 (ap2 IfLf O (ap2 branchesTop a b))))
        e4 = congL IfLf (ap2 branchesTop a b) e2
        e5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 branchesTop a b))
                                 (ap2 IfLf O (ap2 Pair (ap2 dispatch a b) b))))
        e5 = congR IfLf O e3
        e6 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 dispatch a b) b))
                                (ap2 dispatch a b)))
        e6 = axIfLfL (ap2 dispatch a b) b
    in ruleTrans e1 (ruleTrans e4 (ruleTrans e5 e6))

  -- Inner-pair: Fst(Fst a) = Pair _ _ ==> stepProto a b = b.
  stepProto_else : (a b x y : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) (ap2 Pair x y))) ->
    Deriv (atomic (eqn (ap2 stepProto a b) b))
  stepProto_else a b x y discPair =
    let e1 : Deriv (atomic (eqn (ap2 stepProto a b)
                                 (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))))
        e1 = axFan discComb branchesTop IfLf a b
        e2a : Deriv (atomic (eqn (ap2 discComb a b) (ap1 Fst (ap1 Fst a))))
        e2a = discComb_eval a b
        e2 : Deriv (atomic (eqn (ap2 discComb a b) (ap2 Pair x y)))
        e2 = ruleTrans e2a discPair
        e3a : Deriv (atomic (eqn (ap2 branchesTop a b)
                                  (ap2 Pair (ap2 dispatch a b) (ap2 sndProj a b))))
        e3a = axFan dispatch sndProj Pair a b
        e3b : Deriv (atomic (eqn (ap2 sndProj a b) b))
        e3b = sndProj_eval a b
        e3 : Deriv (atomic (eqn (ap2 branchesTop a b)
                                 (ap2 Pair (ap2 dispatch a b) b)))
        e3 = ruleTrans e3a (congR Pair (ap2 dispatch a b) e3b)
        e4 : Deriv (atomic (eqn (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))
                                 (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))))
        e4 = congL IfLf (ap2 branchesTop a b) e2
        e5 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))
                                 (ap2 IfLf (ap2 Pair x y) (ap2 Pair (ap2 dispatch a b) b))))
        e5 = congR IfLf (ap2 Pair x y) e3
        e6 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair (ap2 dispatch a b) b)) b))
        e6 = axIfLfN x y (ap2 dispatch a b) b
    in ruleTrans e1 (ruleTrans e4 (ruleTrans e5 e6))

  ------------------------------------------------------------------
  -- Tag-prefix helpers.

  -- Fst (reify (natCode (suc n))) = O .  Definitionally
  -- reify (natCode (suc n)) = ap2 Pair O (reify (natCode n)).
  fstTagSuc : (n : Nat) ->
    Deriv (atomic (eqn (ap1 Fst (reify (natCode (suc n)))) O))
  fstTagSuc n = axFst O (reify (natCode n))

  -- Open thmT(Pair tagCode payT) into stepProto a b followed by
  -- stepProto_top + the top-level Fst(Fst a) = O reduction.
  dispatchOpens : (n : Nat) (payT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair (reify (natCode (suc n))) payT))
      (ap2 dispatch (ap2 Pair (reify (natCode (suc n))) payT)
                    (ap2 Pair (ap1 thmT (reify (natCode (suc n))))
                              (ap1 thmT payT)))))
  dispatchOpens n payT =
    let tag : Term
        tag = reify (natCode (suc n))
        a : Term
        a = ap2 Pair tag payT
        b : Term
        b = ap2 Pair (ap1 thmT tag) (ap1 thmT payT)
        e1 : Deriv (atomic (eqn (ap1 thmT a) (ap2 stepProto a b)))
        e1 = axRecNd O stepProto tag payT
        f1 : Deriv (atomic (eqn (ap1 Fst a) tag))
        f1 = axFst tag payT
        f2 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) (ap1 Fst tag)))
        f2 = cong1 Fst f1
        fstFstA : Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) O))
        fstFstA = ruleTrans f2 (fstTagSuc n)
        e2 : Deriv (atomic (eqn (ap2 stepProto a b) (ap2 dispatch a b)))
        e2 = stepProto_top a b fstFstA
    in ruleTrans e1 e2

  ------------------------------------------------------------------
  -- Cascade-skip / cascade-hit specialised to a Pair-shaped input.

  -- skipAtTag : at level whose checkTag tests against tagCheck, with
  -- input a = Pair tagInput payload, if  TreeEq tagCheck tagInput =
  -- Pair O O  then the IfLf at this level falls through to the next-
  -- level cascade  nx .

  -- Tree-indexed: tagCheckV is the Tree underlying tagCheck = reify tagCheckV.
  skipAtTag : (tagCheckV : Tree) (tagInput payload b : Term) (body nx : Fun2) ->
    Deriv (atomic (eqn (ap2 TreeEq (reify tagCheckV) tagInput) (ap2 Pair O O))) ->
    Deriv (atomic (eqn
      (ap2 (Fan (Fan (Lift (KT (reify tagCheckV))) (Lift Fst) TreeEq)
                (Fan body nx Pair) IfLf)
           (ap2 Pair tagInput payload) b)
      (ap2 nx (ap2 Pair tagInput payload) b)))
  skipAtTag tagCheckV tagInput payload b body nx neqProof =
    let tagCheck : Term
        tagCheck = reify tagCheckV
        a : Term
        a = ap2 Pair tagInput payload
        chk : Fun2
        chk = Fan (Lift (KT tagCheck)) (Lift Fst) TreeEq
        c1 : Deriv (atomic (eqn (ap2 chk a b)
                                 (ap2 TreeEq (ap2 (Lift (KT tagCheck)) a b)
                                             (ap2 (Lift Fst) a b))))
        c1 = axFan (Lift (KT tagCheck)) (Lift Fst) TreeEq a b
        c2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCheck)) a b) tagCheck))
        c2 = ruleTrans (axLift (KT tagCheck) a b) (axKT tagCheckV a)
        c3 : Deriv (atomic (eqn (ap2 (Lift Fst) a b) (ap1 Fst a)))
        c3 = axLift Fst a b
        c4 : Deriv (atomic (eqn (ap1 Fst a) tagInput))
        c4 = axFst tagInput payload
        c5 : Deriv (atomic (eqn (ap2 TreeEq (ap2 (Lift (KT tagCheck)) a b)
                                            (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCheck (ap2 (Lift Fst) a b))))
        c5 = congL TreeEq (ap2 (Lift Fst) a b) c2
        c6 : Deriv (atomic (eqn (ap2 TreeEq tagCheck (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCheck (ap1 Fst a))))
        c6 = congR TreeEq tagCheck c3
        c7 : Deriv (atomic (eqn (ap2 TreeEq tagCheck (ap1 Fst a))
                                 (ap2 TreeEq tagCheck tagInput)))
        c7 = congR TreeEq tagCheck c4
        chk_to_neq : Deriv (atomic (eqn (ap2 chk a b) (ap2 Pair O O)))
        chk_to_neq = ruleTrans c1 (ruleTrans c5 (ruleTrans c6 (ruleTrans c7 neqProof)))
    in cascadeStep chk body nx a b chk_to_neq

  hitAtTag : (tagCheckV : Tree) (tagInput payload b : Term) (body nx : Fun2) ->
    Deriv (atomic (eqn (ap2 TreeEq (reify tagCheckV) tagInput) O)) ->
    Deriv (atomic (eqn
      (ap2 (Fan (Fan (Lift (KT (reify tagCheckV))) (Lift Fst) TreeEq)
                (Fan body nx Pair) IfLf)
           (ap2 Pair tagInput payload) b)
      (ap2 body (ap2 Pair tagInput payload) b)))
  hitAtTag tagCheckV tagInput payload b body nx eqProof =
    let tagCheck : Term
        tagCheck = reify tagCheckV
        a : Term
        a = ap2 Pair tagInput payload
        chk : Fun2
        chk = Fan (Lift (KT tagCheck)) (Lift Fst) TreeEq
        c1 : Deriv (atomic (eqn (ap2 chk a b)
                                 (ap2 TreeEq (ap2 (Lift (KT tagCheck)) a b)
                                             (ap2 (Lift Fst) a b))))
        c1 = axFan (Lift (KT tagCheck)) (Lift Fst) TreeEq a b
        c2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCheck)) a b) tagCheck))
        c2 = ruleTrans (axLift (KT tagCheck) a b) (axKT tagCheckV a)
        c3 : Deriv (atomic (eqn (ap2 (Lift Fst) a b) (ap1 Fst a)))
        c3 = axLift Fst a b
        c4 : Deriv (atomic (eqn (ap1 Fst a) tagInput))
        c4 = axFst tagInput payload
        c5 : Deriv (atomic (eqn (ap2 TreeEq (ap2 (Lift (KT tagCheck)) a b)
                                            (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCheck (ap2 (Lift Fst) a b))))
        c5 = congL TreeEq (ap2 (Lift Fst) a b) c2
        c6 : Deriv (atomic (eqn (ap2 TreeEq tagCheck (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCheck (ap1 Fst a))))
        c6 = congR TreeEq tagCheck c3
        c7 : Deriv (atomic (eqn (ap2 TreeEq tagCheck (ap1 Fst a))
                                 (ap2 TreeEq tagCheck tagInput)))
        c7 = congR TreeEq tagCheck c4
        chk_to_eq : Deriv (atomic (eqn (ap2 chk a b) O))
        chk_to_eq = ruleTrans c1 (ruleTrans c5 (ruleTrans c6 (ruleTrans c7 eqProof)))
    in cascadeHit chk body nx a b chk_to_eq

  -- Body-Lift-Snd evaluation on a Pair-shaped input.
  bodyLiftSndPair : (tag payT b : Term) ->
    Deriv (atomic (eqn (ap2 (Lift Snd) (ap2 Pair tag payT) b) payT))
  bodyLiftSndPair tag payT b =
    let e1 : Deriv (atomic (eqn (ap2 (Lift Snd) (ap2 Pair tag payT) b)
                                 (ap1 Snd (ap2 Pair tag payT))))
        e1 = axLift Snd (ap2 Pair tag payT) b
        e2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tag payT)) payT))
        e2 = axSnd tag payT
    in ruleTrans e1 e2

  -- ap2 (Lift (KT (reify v))) a b = reify v .  (Tree-indexed.)
  liftKT_eval : (v : Tree) (a b : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (KT (reify v))) a b) (reify v)))
  liftKT_eval v a b = ruleTrans (axLift (KT (reify v)) a b) (axKT v a)

  -- ap2 (Fan (Lift (KT (reify Kv))) X Pair) a b = Pair (reify Kv) xRes
  -- given X a b = xRes.  (Tree-indexed for the constant.)
  pairOfConst_eval : (Kv : Tree) (X : Fun2) (a b xRes : Term) ->
    Deriv (atomic (eqn (ap2 X a b) xRes)) ->
    Deriv (atomic (eqn (ap2 (Fan (Lift (KT (reify Kv))) X Pair) a b)
                       (ap2 Pair (reify Kv) xRes)))
  pairOfConst_eval Kv X a b xRes Xeq =
    let K : Term
        K = reify Kv
        f1 : Deriv (atomic (eqn (ap2 (Fan (Lift (KT K)) X Pair) a b)
                                 (ap2 Pair (ap2 (Lift (KT K)) a b) (ap2 X a b))))
        f1 = axFan (Lift (KT K)) X Pair a b
        kt1 : Deriv (atomic (eqn (ap2 (Lift (KT K)) a b) K))
        kt1 = liftKT_eval Kv a b
        e1 = congL Pair (ap2 X a b) kt1
        e2 = congR Pair K Xeq
    in ruleTrans f1 (ruleTrans e1 e2)

  -- ap2 (Fan X Y Pair) a b = Pair xRes yRes  given X a b = xRes, Y a b = yRes.
  pairOfFan_eval : (X Y : Fun2) (a b xRes yRes : Term) ->
    Deriv (atomic (eqn (ap2 X a b) xRes)) ->
    Deriv (atomic (eqn (ap2 Y a b) yRes)) ->
    Deriv (atomic (eqn (ap2 (Fan X Y Pair) a b) (ap2 Pair xRes yRes)))
  pairOfFan_eval X Y a b xRes yRes Xeq Yeq =
    let f1 : Deriv (atomic (eqn (ap2 (Fan X Y Pair) a b)
                                 (ap2 Pair (ap2 X a b) (ap2 Y a b))))
        f1 = axFan X Y Pair a b
        e1 = congL Pair (ap2 Y a b) Xeq
        e2 = congR Pair xRes Yeq
    in ruleTrans f1 (ruleTrans e1 e2)

  -- Lifted versions (used by lifted dispatchers below).

  pairOfConst_eval_lifted : (P : Formula) (Kv : Tree) (X : Fun2) (a b xRes : Term) ->
    Deriv (P imp atomic (eqn (ap2 X a b) xRes)) ->
    Deriv (P imp atomic (eqn (ap2 (Fan (Lift (KT (reify Kv))) X Pair) a b)
                              (ap2 Pair (reify Kv) xRes)))
  pairOfConst_eval_lifted P Kv X a b xRes Xeq =
    let K : Term
        K = reify Kv
        f1 = axFan (Lift (KT K)) X Pair a b
        kt1 = liftKT_eval Kv a b
        e1 = congL Pair (ap2 X a b) kt1
        lifted_combined : Deriv (P imp atomic (eqn (ap2 (Fan (Lift (KT K)) X Pair) a b)
                                                    (ap2 Pair K (ap2 X a b))))
        lifted_combined = liftAxiom P (ruleTrans f1 e1)
        lifted_e2 : Deriv (P imp atomic (eqn (ap2 Pair K (ap2 X a b))
                                              (ap2 Pair K xRes)))
        lifted_e2 = liftedCongR P Pair (ap2 X a b) xRes K Xeq
    in liftedRuleTrans P
         (ap2 (Fan (Lift (KT K)) X Pair) a b)
         (ap2 Pair K (ap2 X a b))
         (ap2 Pair K xRes)
         lifted_combined lifted_e2

  pairOfFan_eval_lifted : (P : Formula) (X Y : Fun2) (a b xRes yRes : Term) ->
    Deriv (P imp atomic (eqn (ap2 X a b) xRes)) ->
    Deriv (P imp atomic (eqn (ap2 Y a b) yRes)) ->
    Deriv (P imp atomic (eqn (ap2 (Fan X Y Pair) a b) (ap2 Pair xRes yRes)))
  pairOfFan_eval_lifted P X Y a b xRes yRes Xeq Yeq =
    let f1 = axFan X Y Pair a b
        lifted_f1 : Deriv (P imp atomic (eqn (ap2 (Fan X Y Pair) a b)
                                              (ap2 Pair (ap2 X a b)(ap2 Y a b))))
        lifted_f1 = liftAxiom P f1
        lifted_e1 : Deriv (P imp atomic (eqn (ap2 Pair (ap2 X a b)(ap2 Y a b))
                                              (ap2 Pair xRes (ap2 Y a b))))
        lifted_e1 = liftedCongL P Pair (ap2 X a b) xRes (ap2 Y a b) Xeq
        lifted_e2 : Deriv (P imp atomic (eqn (ap2 Pair xRes (ap2 Y a b))
                                              (ap2 Pair xRes yRes)))
        lifted_e2 = liftedCongR P Pair (ap2 Y a b) yRes xRes Yeq
    in liftedRuleTrans P
         (ap2 (Fan X Y Pair) a b)
         (ap2 Pair (ap2 X a b)(ap2 Y a b))
         (ap2 Pair xRes yRes)
         lifted_f1
         (liftedRuleTrans P
           (ap2 Pair (ap2 X a b)(ap2 Y a b))
           (ap2 Pair xRes (ap2 Y a b))
           (ap2 Pair xRes yRes)
           lifted_e1 lifted_e2)

  -- ap2 (Lift (Comp Fst Snd)) (Pair tag (Pair x y)) b = x .
  liftCompFstSnd_evalPair : (tag x y b : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd))
                              (ap2 Pair tag (ap2 Pair x y)) b) x))
  liftCompFstSnd_evalPair tag x y b =
    let a    : Term
        a    = ap2 Pair tag (ap2 Pair x y)
        e1 : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a b)
                                 (ap1 (Comp Fst Snd) a)))
        e1 = axLift (Comp Fst Snd) a b
        e2 : Deriv (atomic (eqn (ap1 (Comp Fst Snd) a) (ap1 Fst (ap1 Snd a))))
        e2 = axComp Fst Snd a
        e3 : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair x y)))
        e3 = axSnd tag (ap2 Pair x y)
        e4 : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap1 Fst (ap2 Pair x y))))
        e4 = cong1 Fst e3
        e5 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair x y)) x))
        e5 = axFst x y
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e4 e5))

  -- ap2 (Lift (Comp Snd Snd)) (Pair tag (Pair x y)) b = y .
  liftCompSndSnd_evalPair : (tag x y b : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (Comp Snd Snd))
                              (ap2 Pair tag (ap2 Pair x y)) b) y))
  liftCompSndSnd_evalPair tag x y b =
    let a    : Term
        a    = ap2 Pair tag (ap2 Pair x y)
        e1 : Deriv (atomic (eqn (ap2 (Lift (Comp Snd Snd)) a b)
                                 (ap1 (Comp Snd Snd) a)))
        e1 = axLift (Comp Snd Snd) a b
        e2 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) a) (ap1 Snd (ap1 Snd a))))
        e2 = axComp Snd Snd a
        e3 : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair x y)))
        e3 = axSnd tag (ap2 Pair x y)
        e4 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd a)) (ap1 Snd (ap2 Pair x y))))
        e4 = cong1 Snd e3
        e5 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair x y)) y))
        e5 = axSnd x y
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e4 e5))

  -- Composition glue: ap2 (Lift (Comp f g)) a b = val
  -- given ap1 g a = inner and ap1 f inner = val.
  liftComp_eval : (f g : Fun1) (a b inner val : Term) ->
    Deriv (atomic (eqn (ap1 g a) inner)) ->
    Deriv (atomic (eqn (ap1 f inner) val)) ->
    Deriv (atomic (eqn (ap2 (Lift (Comp f g)) a b) val))
  liftComp_eval f g a b inner val gEq fEq =
    let e1 : Deriv (atomic (eqn (ap2 (Lift (Comp f g)) a b)
                                 (ap1 (Comp f g) a)))
        e1 = axLift (Comp f g) a b
        e2 : Deriv (atomic (eqn (ap1 (Comp f g) a) (ap1 f (ap1 g a))))
        e2 = axComp f g a
        e3 : Deriv (atomic (eqn (ap1 f (ap1 g a)) (ap1 f inner)))
        e3 = cong1 f gEq
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 fEq))

  ------------------------------------------------------------------
  -- Snd-chain evaluators on stratified payloads.
  --
  -- Naming: sndOf_dN  maps a = Pair tag (depth-N pair-chain) to the
  -- result of  (Snd^N a) , i.e. the rightmost depth-N payload component.

  -- ap1 Snd a = pay   when  a = Pair tag pay.
  sndOf_d1 : (tag pay : Term) ->
    Deriv (atomic (eqn (ap1 Snd (ap2 Pair tag pay)) pay))
  sndOf_d1 tag pay = axSnd tag pay

  -- ap1 Snd (ap1 Snd a) = rest  when  a = Pair tag (Pair x rest).
  sndOf_d2 : (tag x rest : Term) ->
    Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair tag (ap2 Pair x rest)))) rest))
  sndOf_d2 tag x rest =
    let s1 = sndOf_d1 tag (ap2 Pair x rest)
        s2 = cong1 Snd s1
        s3 = sndOf_d1 x rest
    in ruleTrans s2 s3

  -- ap1 Snd (ap1 Snd (ap1 Snd a)) = rest  when a = Pair tag (Pair x1 (Pair x2 rest)).
  sndOf_d3 : (tag x1 x2 rest : Term) ->
    Deriv (atomic (eqn
      (ap1 Snd (ap1 Snd (ap1 Snd
        (ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 rest))))))
      rest))
  sndOf_d3 tag x1 x2 rest =
    let s1 = sndOf_d2 tag x1 (ap2 Pair x2 rest)
        s2 = cong1 Snd s1
        s3 = sndOf_d1 x2 rest
    in ruleTrans s2 s3

  sndOf_d4 : (tag x1 x2 x3 rest : Term) ->
    Deriv (atomic (eqn
      (ap1 Snd (ap1 Snd (ap1 Snd (ap1 Snd
        (ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 rest))))))))
      rest))
  sndOf_d4 tag x1 x2 x3 rest =
    let s1 = sndOf_d3 tag x1 x2 (ap2 Pair x3 rest)
        s2 = cong1 Snd s1
        s3 = sndOf_d1 x3 rest
    in ruleTrans s2 s3

  ------------------------------------------------------------------
  -- Position-extractors at depths 3, 4, 5.

  -- Depth 3 payload: a = Pair tag (Pair x1 (Pair x2 x3)).

  liftFstSndSnd_evalPair3 : (tag x1 x2 x3 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Fst (Comp Snd Snd)))
            (ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 x3))) b)
      x2))
  liftFstSndSnd_evalPair3 tag x1 x2 x3 b =
    let a = ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 x3))
        snd2 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) a) (ap2 Pair x2 x3)))
        snd2 =
          let c1 = axComp Snd Snd a
              c2 = sndOf_d2 tag x1 (ap2 Pair x2 x3)
          in ruleTrans c1 c2
    in liftComp_eval Fst (Comp Snd Snd) a b (ap2 Pair x2 x3) x2 snd2 (axFst x2 x3)

  liftSndSndSnd_evalPair3 : (tag x1 x2 x3 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Snd (Comp Snd Snd)))
            (ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 x3))) b)
      x3))
  liftSndSndSnd_evalPair3 tag x1 x2 x3 b =
    let a = ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 x3))
        snd2 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) a) (ap2 Pair x2 x3)))
        snd2 =
          let c1 = axComp Snd Snd a
              c2 = sndOf_d2 tag x1 (ap2 Pair x2 x3)
          in ruleTrans c1 c2
    in liftComp_eval Snd (Comp Snd Snd) a b (ap2 Pair x2 x3) x3 snd2 (axSnd x2 x3)

  -- Depth 4 payload: a = Pair tag (Pair x1 (Pair x2 (Pair x3 x4))).

  liftFstSndSndSnd_evalPair4 : (tag x1 x2 x3 x4 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
            (ap2 Pair tag
              (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 x4)))) b)
      x3))
  liftFstSndSndSnd_evalPair4 tag x1 x2 x3 x4 b =
    let a = ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 x4)))
        c1 = axComp Snd (Comp Snd Snd) a
                -- (Comp Snd (Comp Snd Snd)) a = Snd ((Comp Snd Snd) a)
        c2 = axComp Snd Snd a
                -- (Comp Snd Snd) a = Snd (Snd a)
        c3 = cong1 Snd c2
                -- Snd ((Comp Snd Snd) a) = Snd (Snd (Snd a))
        c4 = sndOf_d3 tag x1 x2 (ap2 Pair x3 x4)
                -- Snd (Snd (Snd a)) = Pair x3 x4
        snd3 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd Snd)) a)
                                   (ap2 Pair x3 x4)))
        snd3 = ruleTrans c1 (ruleTrans c3 c4)
    in liftComp_eval Fst (Comp Snd (Comp Snd Snd)) a b
         (ap2 Pair x3 x4) x3 snd3 (axFst x3 x4)

  liftSndSndSndSnd_evalPair4 : (tag x1 x2 x3 x4 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
            (ap2 Pair tag
              (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 x4)))) b)
      x4))
  liftSndSndSndSnd_evalPair4 tag x1 x2 x3 x4 b =
    let a = ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 x4)))
        c1 = axComp Snd (Comp Snd Snd) a
        c2 = axComp Snd Snd a
        c3 = cong1 Snd c2
        c4 = sndOf_d3 tag x1 x2 (ap2 Pair x3 x4)
        snd3 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd Snd)) a)
                                   (ap2 Pair x3 x4)))
        snd3 = ruleTrans c1 (ruleTrans c3 c4)
    in liftComp_eval Snd (Comp Snd (Comp Snd Snd)) a b
         (ap2 Pair x3 x4) x4 snd3 (axSnd x3 x4)

  -- Depth 5 payload: a = Pair tag (Pair x1 (Pair x2 (Pair x3 (Pair x4 x5)))).

  liftFstSndSndSndSnd_evalPair5 : (tag x1 x2 x3 x4 x5 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
            (ap2 Pair tag
              (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 (ap2 Pair x4 x5))))) b)
      x4))
  liftFstSndSndSndSnd_evalPair5 tag x1 x2 x3 x4 x5 b =
    let a = ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 (ap2 Pair x4 x5))))
        c1 = axComp Snd (Comp Snd (Comp Snd Snd)) a
        c2 = axComp Snd (Comp Snd Snd) a
        c3 = cong1 Snd c2
        c4 = axComp Snd Snd a
        c5 = cong1 Snd (cong1 Snd c4)
        c6 = sndOf_d4 tag x1 x2 x3 (ap2 Pair x4 x5)
        snd4 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd (Comp Snd Snd))) a)
                                   (ap2 Pair x4 x5)))
        snd4 = ruleTrans c1 (ruleTrans c3 (ruleTrans c5 c6))
    in liftComp_eval Fst (Comp Snd (Comp Snd (Comp Snd Snd))) a b
         (ap2 Pair x4 x5) x4 snd4 (axFst x4 x5)

  liftSndSndSndSndSnd_evalPair5 : (tag x1 x2 x3 x4 x5 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
            (ap2 Pair tag
              (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 (ap2 Pair x4 x5))))) b)
      x5))
  liftSndSndSndSndSnd_evalPair5 tag x1 x2 x3 x4 x5 b =
    let a = ap2 Pair tag (ap2 Pair x1 (ap2 Pair x2 (ap2 Pair x3 (ap2 Pair x4 x5))))
        c1 = axComp Snd (Comp Snd (Comp Snd Snd)) a
        c2 = axComp Snd (Comp Snd Snd) a
        c3 = cong1 Snd c2
        c4 = axComp Snd Snd a
        c5 = cong1 Snd (cong1 Snd c4)
        c6 = sndOf_d4 tag x1 x2 x3 (ap2 Pair x4 x5)
        snd4 : Deriv (atomic (eqn (ap1 (Comp Snd (Comp Snd (Comp Snd Snd))) a)
                                   (ap2 Pair x4 x5)))
        snd4 = ruleTrans c1 (ruleTrans c3 (ruleTrans c5 c6))
    in liftComp_eval Snd (Comp Snd (Comp Snd (Comp Snd Snd))) a b
         (ap2 Pair x4 x5) x5 snd4 (axSnd x4 x5)

  ------------------------------------------------------------------
  -- Group I dispatch lemmas (10 tags: axI, axFst, axSnd, axConst,
  -- axComp, axComp2, axLift, axPost, axFan, axKT).
  --
  -- Each proof has the same shape:
  --   1. dispatchOpens : thmT(reify(encX args)) = dispatch a b .
  --   2. M-1 skipAtTag applications (one per tag below this one).
  --   3. 1 hitAtTag application at this tag.
  --   4. bodyLiftSndPair : body_X a b = payT .
  -- Total chain length grows linearly with the tag's position.

  -- Group I body-evaluation lemmas: each shows
  --   ap2 body_X (Pair tagCode_X payT) b  =  reify (outX args) .
  -- Used inside the corresponding thmTDispX dispatch lemma.

  body_axI_eval : (t b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axI (ap2 Pair tagCode_axI (reify (code t))) b)
      (reify (outAxI t))))
  body_axI_eval t b =
    let payT  = reify (code t)
        a     = ap2 Pair tagCode_axI payT
        K1V   = tagAp1               -- Tree
        K2V   = codeF1 I             -- Tree
        K1    = reify K1V            -- Term form
        K2    = reify K2V            -- Term form
        snd_a = bodyLiftSndPair tagCode_axI payT b
        innerKT_red = pairOfConst_eval K2V (Lift Snd) a b payT snd_a
        outerKT_red = pairOfConst_eval K1V
                        (Fan (Lift (KT K2)) (Lift Snd) Pair)
                        a b (ap2 Pair K2 payT) innerKT_red
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2)) (Lift Snd) Pair)
              Pair)
         (Lift Snd) a b
         (ap2 Pair K1 (ap2 Pair K2 payT)) payT
         outerKT_red snd_a

  thmTDispAxI : (t : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxI t))) (reify (outAxI t))))
  thmTDispAxI t =
    let payT : Term
        payT = reify (code t)
        a : Term
        a = ap2 Pair tagCode_axI payT
        b : Term
        b = ap2 Pair (ap1 thmT tagCode_axI) (ap1 thmT payT)
        e1 : Deriv (atomic (eqn (ap1 thmT a) (ap2 dispatch a b)))
        e1 = dispatchOpens zero payT
        e2 : Deriv (atomic (eqn (ap2 dispatch a b) (ap2 body_axI a b)))
        e2 = hitAtTag (natCode tagAxI) tagCode_axI payT b body_axI next_axI (teqEq tagAxI)
        e3 : Deriv (atomic (eqn (ap2 body_axI a b) (reify (outAxI t))))
        e3 = body_axI_eval t b
    in ruleTrans e1 (ruleTrans e2 e3)

  -- Parametric variant of body_axI_eval (Theorem 12 / Parts/I.agda).
  body_axI_eval_param : (xT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axI (ap2 Pair tagCode_axI xT) bb)
      (ap2 Pair (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 I)) xT)) xT)))
  body_axI_eval_param xT bb =
    let payT  = xT
        a     = ap2 Pair tagCode_axI payT
        K1V   = tagAp1
        K2V   = codeF1 I
        K1    = reify K1V
        K2    = reify K2V
        snd_a = bodyLiftSndPair tagCode_axI payT bb
        innerKT_red = pairOfConst_eval K2V (Lift Snd) a bb payT snd_a
        outerKT_red = pairOfConst_eval K1V
                        (Fan (Lift (KT K2)) (Lift Snd) Pair)
                        a bb (ap2 Pair K2 payT) innerKT_red
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2)) (Lift Snd) Pair)
              Pair)
         (Lift Snd) a bb
         (ap2 Pair K1 (ap2 Pair K2 payT)) payT
         outerKT_red snd_a

  -- Parametric variant of thmTDispAxI (Theorem 12 / Parts/I.agda).
  thmTDispAxI_param : (xT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axI xT))
      (ap2 Pair (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 I)) xT)) xT)))
  thmTDispAxI_param xT =
    let payT = xT
        a   = ap2 Pair tagCode_axI payT
        b   = ap2 Pair (ap1 thmT tagCode_axI) (ap1 thmT payT)
        e1  = dispatchOpens zero payT
        e2  = hitAtTag (natCode tagAxI) tagCode_axI payT b body_axI next_axI (teqEq tagAxI)
        e3  = body_axI_eval_param xT b
    in ruleTrans e1 (ruleTrans e2 e3)

  body_axFst_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFst
            (ap2 Pair tagCode_axFst (reify (nd (code a') (code b')))) bb)
      (reify (outAxFst a' b'))))
  body_axFst_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axFst payT
        K1V    = tagAp1                            -- Tree
        K2V    = codeF1 Fst                        -- Tree
        K3V    = tagAp2                            -- Tree
        K4V    = codeF2 Pair                       -- Tree
        K1     = reify K1V                         -- Term form
        K2     = reify K2V
        K3     = reify K3V
        K4     = reify K4V
        snd_a  = bodyLiftSndPair tagCode_axFst payT bb
        fstSnd_a : Deriv (atomic (eqn
                            (ap2 (Lift (Comp Fst Snd)) a bb) payAT))
        fstSnd_a = liftCompFstSnd_evalPair tagCode_axFst payAT payBT bb
        -- Build chain bottom-up: Pair K4 payT, Pair K3 (...), Pair K2 (...), Pair K1 (...).
        l4 = pairOfConst_eval K4V (Lift Snd) a bb payT snd_a
        l3 = pairOfConst_eval K3V
                 (Fan (Lift (KT K4)) (Lift Snd) Pair) a bb
                 (ap2 Pair K4 payT) l4
        l2 = pairOfConst_eval K2V
                 (Fan (Lift (KT K3))
                      (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) a bb
                 (ap2 Pair K3 (ap2 Pair K4 payT)) l3
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2))
                      (Fan (Lift (KT K3))
                           (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) a bb
                 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2))
                   (Fan (Lift (KT K3))
                        (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT)))) payAT
         l1 fstSnd_a

  thmTDispAxFst : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxFst a' b')))
                       (reify (outAxFst a' b'))))
  thmTDispAxFst a' b' =
    let payT = reify (nd (code a') (code b'))
        a   = ap2 Pair tagCode_axFst payT
        b   = ap2 Pair (ap1 thmT tagCode_axFst) (ap1 thmT payT)
        e1  = dispatchOpens tagAxI payT
        s1  = skipAtTag (natCode tagAxI) tagCode_axFst payT b body_axI next_axI
                 (teqDiff tagAxI tagAxFst refl)
        h   = hitAtTag (natCode tagAxFst) tagCode_axFst payT b body_axFst next_axFst
                 (teqEq tagAxFst)
        be  = body_axFst_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans h be))

  -- Parametric variant of body_axFst_eval (Theorem 12 / Parts/Fst.agda).
  body_axFst_eval_param : (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFst (ap2 Pair tagCode_axFst (ap2 Pair aT bT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 Fst))
            (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 Pair))
                (ap2 Pair aT bT)))))
        aT)))
  body_axFst_eval_param aT bT bb =
    let payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axFst payT
        K1V    = tagAp1
        K2V    = codeF1 Fst
        K3V    = tagAp2
        K4V    = codeF2 Pair
        K1     = reify K1V
        K2     = reify K2V
        K3     = reify K3V
        K4     = reify K4V
        snd_a  = bodyLiftSndPair tagCode_axFst payT bb
        fstSnd_a : Deriv (atomic (eqn
                            (ap2 (Lift (Comp Fst Snd)) a bb) payAT))
        fstSnd_a = liftCompFstSnd_evalPair tagCode_axFst payAT payBT bb
        l4 = pairOfConst_eval K4V (Lift Snd) a bb payT snd_a
        l3 = pairOfConst_eval K3V
                 (Fan (Lift (KT K4)) (Lift Snd) Pair) a bb
                 (ap2 Pair K4 payT) l4
        l2 = pairOfConst_eval K2V
                 (Fan (Lift (KT K3))
                      (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) a bb
                 (ap2 Pair K3 (ap2 Pair K4 payT)) l3
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2))
                      (Fan (Lift (KT K3))
                           (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) a bb
                 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2))
                   (Fan (Lift (KT K3))
                        (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT)))) payAT
         l1 fstSnd_a

  -- Parametric variant of thmTDispAxFst.
  thmTDispAxFst_param : (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axFst (ap2 Pair aT bT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 Fst))
            (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 Pair))
                (ap2 Pair aT bT)))))
        aT)))
  thmTDispAxFst_param aT bT =
    let payT = ap2 Pair aT bT
        a   = ap2 Pair tagCode_axFst payT
        b   = ap2 Pair (ap1 thmT tagCode_axFst) (ap1 thmT payT)
        e1  = dispatchOpens tagAxI payT
        s1  = skipAtTag (natCode tagAxI) tagCode_axFst payT b body_axI next_axI
                 (teqDiff tagAxI tagAxFst refl)
        h   = hitAtTag (natCode tagAxFst) tagCode_axFst payT b body_axFst next_axFst
                 (teqEq tagAxFst)
        be  = body_axFst_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans h be))

  body_axSnd_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axSnd
            (ap2 Pair tagCode_axSnd (reify (nd (code a') (code b')))) bb)
      (reify (outAxSnd a' b'))))
  body_axSnd_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axSnd payT
        K1V    = tagAp1
        K2V    = codeF1 Snd
        K3V    = tagAp2
        K4V    = codeF2 Pair
        K1     = reify K1V
        K2     = reify K2V
        K3     = reify K3V
        K4     = reify K4V
        snd_a  = bodyLiftSndPair tagCode_axSnd payT bb
        sndSnd_a : Deriv (atomic (eqn
                            (ap2 (Lift (Comp Snd Snd)) a bb) payBT))
        sndSnd_a = liftCompSndSnd_evalPair tagCode_axSnd payAT payBT bb
        l4 = pairOfConst_eval K4V (Lift Snd) a bb payT snd_a
        l3 = pairOfConst_eval K3V
                 (Fan (Lift (KT K4)) (Lift Snd) Pair) a bb
                 (ap2 Pair K4 payT) l4
        l2 = pairOfConst_eval K2V
                 (Fan (Lift (KT K3))
                      (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) a bb
                 (ap2 Pair K3 (ap2 Pair K4 payT)) l3
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2))
                      (Fan (Lift (KT K3))
                           (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) a bb
                 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2))
                   (Fan (Lift (KT K3))
                        (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) Pair)
         (Lift (Comp Snd Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT)))) payBT
         l1 sndSnd_a

  thmTDispAxSnd : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxSnd a' b')))
                       (reify (outAxSnd a' b'))))
  thmTDispAxSnd a' b' =
    let payT = reify (nd (code a') (code b'))
        a   = ap2 Pair tagCode_axSnd payT
        b   = ap2 Pair (ap1 thmT tagCode_axSnd) (ap1 thmT payT)
        e1  = dispatchOpens tagAxFst payT
        s1  = skipAtTag (natCode tagAxI)    tagCode_axSnd payT b body_axI    next_axI
                 (teqDiff tagAxI    tagAxSnd refl)
        s2  = skipAtTag (natCode tagAxFst)  tagCode_axSnd payT b body_axFst  next_axFst
                 (teqDiff tagAxFst  tagAxSnd refl)
        h   = hitAtTag  (natCode tagAxSnd)  tagCode_axSnd payT b body_axSnd  next_axSnd
                 (teqEq tagAxSnd)
        be  = body_axSnd_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans h be)))

  -- Parametric variant of body_axSnd_eval (Theorem 12 / Parts/Snd.agda).
  body_axSnd_eval_param : (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axSnd (ap2 Pair tagCode_axSnd (ap2 Pair aT bT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 Snd))
            (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 Pair))
                (ap2 Pair aT bT)))))
        bT)))
  body_axSnd_eval_param aT bT bb =
    let payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axSnd payT
        K1V    = tagAp1
        K2V    = codeF1 Snd
        K3V    = tagAp2
        K4V    = codeF2 Pair
        K1     = reify K1V
        K2     = reify K2V
        K3     = reify K3V
        K4     = reify K4V
        snd_a  = bodyLiftSndPair tagCode_axSnd payT bb
        sndSnd_a : Deriv (atomic (eqn
                            (ap2 (Lift (Comp Snd Snd)) a bb) payBT))
        sndSnd_a = liftCompSndSnd_evalPair tagCode_axSnd payAT payBT bb
        l4 = pairOfConst_eval K4V (Lift Snd) a bb payT snd_a
        l3 = pairOfConst_eval K3V
                 (Fan (Lift (KT K4)) (Lift Snd) Pair) a bb
                 (ap2 Pair K4 payT) l4
        l2 = pairOfConst_eval K2V
                 (Fan (Lift (KT K3))
                      (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) a bb
                 (ap2 Pair K3 (ap2 Pair K4 payT)) l3
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2))
                      (Fan (Lift (KT K3))
                           (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) a bb
                 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2))
                   (Fan (Lift (KT K3))
                        (Fan (Lift (KT K4)) (Lift Snd) Pair) Pair) Pair) Pair)
         (Lift (Comp Snd Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 (ap2 Pair K3 (ap2 Pair K4 payT)))) payBT
         l1 sndSnd_a

  -- Parametric variant of thmTDispAxSnd.
  thmTDispAxSnd_param : (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axSnd (ap2 Pair aT bT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 Snd))
            (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 Pair))
                (ap2 Pair aT bT)))))
        bT)))
  thmTDispAxSnd_param aT bT =
    let payT = ap2 Pair aT bT
        a   = ap2 Pair tagCode_axSnd payT
        b   = ap2 Pair (ap1 thmT tagCode_axSnd) (ap1 thmT payT)
        e1  = dispatchOpens tagAxFst payT
        s1  = skipAtTag (natCode tagAxI)    tagCode_axSnd payT b body_axI    next_axI
                 (teqDiff tagAxI    tagAxSnd refl)
        s2  = skipAtTag (natCode tagAxFst)  tagCode_axSnd payT b body_axFst  next_axFst
                 (teqDiff tagAxFst  tagAxSnd refl)
        h   = hitAtTag  (natCode tagAxSnd)  tagCode_axSnd payT b body_axSnd  next_axSnd
                 (teqEq tagAxSnd)
        be  = body_axSnd_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans h be)))

  body_axConst_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axConst
            (ap2 Pair tagCode_axConst (reify (nd (code a') (code b')))) bb)
      (reify (outAxConst a' b'))))
  body_axConst_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axConst payT
        K1V    = tagAp2
        K2V    = codeF2 Const
        K1     = reify K1V
        K2     = reify K2V
        snd_a  = bodyLiftSndPair tagCode_axConst payT bb
        fstSnd_a = liftCompFstSnd_evalPair tagCode_axConst payAT payBT bb
        l2 = pairOfConst_eval K2V (Lift Snd) a bb payT snd_a
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2)) (Lift Snd) Pair) a bb
                 (ap2 Pair K2 payT) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2)) (Lift Snd) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 payT)) payAT
         l1 fstSnd_a

  thmTDispAxConst : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxConst a' b')))
                       (reify (outAxConst a' b'))))
  thmTDispAxConst a' b' =
    let payT = reify (nd (code a') (code b'))
        a   = ap2 Pair tagCode_axConst payT
        b   = ap2 Pair (ap1 thmT tagCode_axConst) (ap1 thmT payT)
        e1  = dispatchOpens tagAxSnd payT
        s1  = skipAtTag (natCode tagAxI)    tagCode_axConst payT b body_axI    next_axI
                 (teqDiff tagAxI    tagAxConst refl)
        s2  = skipAtTag (natCode tagAxFst)  tagCode_axConst payT b body_axFst  next_axFst
                 (teqDiff tagAxFst  tagAxConst refl)
        s3  = skipAtTag (natCode tagAxSnd)  tagCode_axConst payT b body_axSnd  next_axSnd
                 (teqDiff tagAxSnd  tagAxConst refl)
        h   = hitAtTag  (natCode tagAxConst) tagCode_axConst payT b body_axConst next_axConst
                 (teqEq tagAxConst)
        be  = body_axConst_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans h be))))

  -- Parametric variant of body_axConst_eval (Theorem 12 / Parts/Const.agda).
  body_axConst_eval_param : (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axConst (ap2 Pair tagCode_axConst (ap2 Pair aT bT)) bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Const))
                                    (ap2 Pair aT bT))) aT)))
  body_axConst_eval_param aT bT bb =
    let payT   = ap2 Pair aT bT
        a      = ap2 Pair tagCode_axConst payT
        K1V    = tagAp2
        K2V    = codeF2 Const
        K1     = reify K1V
        K2     = reify K2V
        snd_a  = bodyLiftSndPair tagCode_axConst payT bb
        fstSnd_a = liftCompFstSnd_evalPair tagCode_axConst aT bT bb
        l2 = pairOfConst_eval K2V (Lift Snd) a bb payT snd_a
        l1 = pairOfConst_eval K1V
                 (Fan (Lift (KT K2)) (Lift Snd) Pair) a bb
                 (ap2 Pair K2 payT) l2
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Lift (KT K2)) (Lift Snd) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K1 (ap2 Pair K2 payT)) aT
         l1 fstSnd_a

  -- Parametric variant of thmTDispAxConst.
  thmTDispAxConst_param : (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axConst (ap2 Pair aT bT)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 Const))
                                    (ap2 Pair aT bT))) aT)))
  thmTDispAxConst_param aT bT =
    let payT = ap2 Pair aT bT
        a   = ap2 Pair tagCode_axConst payT
        b   = ap2 Pair (ap1 thmT tagCode_axConst) (ap1 thmT payT)
        e1  = dispatchOpens tagAxSnd payT
        s1  = skipAtTag (natCode tagAxI)    tagCode_axConst payT b body_axI    next_axI
                 (teqDiff tagAxI    tagAxConst refl)
        s2  = skipAtTag (natCode tagAxFst)  tagCode_axConst payT b body_axFst  next_axFst
                 (teqDiff tagAxFst  tagAxConst refl)
        s3  = skipAtTag (natCode tagAxSnd)  tagCode_axConst payT b body_axSnd  next_axSnd
                 (teqDiff tagAxSnd  tagAxConst refl)
        h   = hitAtTag  (natCode tagAxConst) tagCode_axConst payT b body_axConst next_axConst
                 (teqEq tagAxConst)
        be  = body_axConst_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans h be))))

  body_axComp_eval : (f g : Fun1) (t bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axComp
            (ap2 Pair tagCode_axComp
                       (reify (nd (codeF1 f) (nd (codeF1 g) (code t))))) bb)
      (reify (outAxComp f g t))))
  body_axComp_eval f g t bb =
    let cf = reify (codeF1 f)
        cg = reify (codeF1 g)
        ct = reify (code t)
        payT = ap2 Pair cf (ap2 Pair cg ct)
        a    = ap2 Pair tagCode_axComp payT
        K1V  = tagAp1
        K2V  = leftT (codeF1 (Comp I I))
        K1   = reify K1V
        K2   = reify K2V
        ext_cf = liftCompFstSnd_evalPair tagCode_axComp cf (ap2 Pair cg ct) bb
        ext_cg = liftFstSndSnd_evalPair3 tagCode_axComp cf cg ct bb
        ext_ct = liftSndSndSnd_evalPair3 tagCode_axComp cf cg ct bb
        -- LHS = Pair K1 (Pair (Pair K2 (Pair cf cg)) ct)
        cfcg = pairOfFan_eval
                 (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd Snd))) a bb cf cg ext_cf ext_cg
        kcfcg = pairOfConst_eval K2V
                 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Fst (Comp Snd Snd))) Pair) a bb
                 (ap2 Pair cf cg) cfcg
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K2))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd Snd))) a bb
                   (ap2 Pair K2 (ap2 Pair cf cg)) ct kcfcg ext_ct
        lhsBuild = pairOfConst_eval K1V
                     (Fan (Fan (Lift (KT K2))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                          (Lift (Comp Snd (Comp Snd Snd))) Pair) a bb
                     (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) ct) midLHS
        -- RHS = Pair K1 (Pair cf (Pair K1 (Pair cg ct)))
        cgct = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd Snd))) a bb cg ct ext_cg ext_ct
        kcgct = pairOfConst_eval K1V
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair) a bb
                  (ap2 Pair cg ct) cgct
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K1))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   a bb cf (ap2 Pair K1 (ap2 Pair cg ct)) ext_cf kcgct
        rhsBuild = pairOfConst_eval K1V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (KT K1))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                          Pair) a bb
                     (ap2 Pair cf (ap2 Pair K1 (ap2 Pair cg ct))) midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Fan (Lift (KT K2))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
         (Fan (Lift (KT K1))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K1))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair)
              Pair)
         a bb
         (ap2 Pair K1 (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) ct))
         (ap2 Pair K1 (ap2 Pair cf (ap2 Pair K1 (ap2 Pair cg ct))))
         lhsBuild rhsBuild

  thmTDispAxComp : (f g : Fun1) (t : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxComp f g t)))
                       (reify (outAxComp f g t))))
  thmTDispAxComp f g t =
    let payT = reify (nd (codeF1 f) (nd (codeF1 g) (code t)))
        a   = ap2 Pair tagCode_axComp payT
        b   = ap2 Pair (ap1 thmT tagCode_axComp) (ap1 thmT payT)
        e1  = dispatchOpens tagAxConst payT
        s1  = skipAtTag (natCode tagAxI)     tagCode_axComp payT b body_axI     next_axI
                 (teqDiff tagAxI     tagAxComp refl)
        s2  = skipAtTag (natCode tagAxFst)   tagCode_axComp payT b body_axFst   next_axFst
                 (teqDiff tagAxFst   tagAxComp refl)
        s3  = skipAtTag (natCode tagAxSnd)   tagCode_axComp payT b body_axSnd   next_axSnd
                 (teqDiff tagAxSnd   tagAxComp refl)
        s4  = skipAtTag (natCode tagAxConst) tagCode_axComp payT b body_axConst next_axConst
                 (teqDiff tagAxConst tagAxComp refl)
        h   = hitAtTag  (natCode tagAxComp)  tagCode_axComp payT b body_axComp  next_axComp
                 (teqEq tagAxComp)
        be  = body_axComp_eval f g t b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans h be)))))

  -- Parametric variant of body_axComp_eval (Theorem 12 / Parts/Comp.agda).
  body_axComp_eval_param : (f g : Fun1) (xT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axComp
            (ap2 Pair tagCode_axComp
              (ap2 Pair (reify (codeF1 f))
                (ap2 Pair (reify (codeF1 g)) xT))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp I I))))
                              (ap2 Pair (reify (codeF1 f))
                                        (reify (codeF1 g))))
                    xT))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 f))
            (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 g)) xT)))))))
  body_axComp_eval_param f g xT bb =
    let cf = reify (codeF1 f)
        cg = reify (codeF1 g)
        payT = ap2 Pair cf (ap2 Pair cg xT)
        a    = ap2 Pair tagCode_axComp payT
        K1V  = tagAp1
        K2V  = leftT (codeF1 (Comp I I))
        K1   = reify K1V
        K2   = reify K2V
        ext_cf = liftCompFstSnd_evalPair tagCode_axComp cf (ap2 Pair cg xT) bb
        ext_cg = liftFstSndSnd_evalPair3 tagCode_axComp cf cg xT bb
        ext_xT = liftSndSndSnd_evalPair3 tagCode_axComp cf cg xT bb
        cfcg = pairOfFan_eval
                 (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd Snd))) a bb cf cg ext_cf ext_cg
        kcfcg = pairOfConst_eval K2V
                 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Fst (Comp Snd Snd))) Pair) a bb
                 (ap2 Pair cf cg) cfcg
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K2))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd Snd))) a bb
                   (ap2 Pair K2 (ap2 Pair cf cg)) xT kcfcg ext_xT
        lhsBuild = pairOfConst_eval K1V
                     (Fan (Fan (Lift (KT K2))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                          (Lift (Comp Snd (Comp Snd Snd))) Pair) a bb
                     (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) xT) midLHS
        cgxT = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd Snd))) a bb cg xT ext_cg ext_xT
        kcgxT = pairOfConst_eval K1V
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair) a bb
                  (ap2 Pair cg xT) cgxT
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K1))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   a bb cf (ap2 Pair K1 (ap2 Pair cg xT)) ext_cf kcgxT
        rhsBuild = pairOfConst_eval K1V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (KT K1))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                          Pair) a bb
                     (ap2 Pair cf (ap2 Pair K1 (ap2 Pair cg xT))) midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Fan (Lift (KT K2))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
         (Fan (Lift (KT K1))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K1))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   Pair) Pair)
         a bb
         (ap2 Pair K1 (ap2 Pair (ap2 Pair K2 (ap2 Pair cf cg)) xT))
         (ap2 Pair K1 (ap2 Pair cf (ap2 Pair K1 (ap2 Pair cg xT))))
         lhsBuild rhsBuild

  -- Parametric variant of thmTDispAxComp.
  thmTDispAxComp_param : (f g : Fun1) (xT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axComp
                          (ap2 Pair (reify (codeF1 f))
                            (ap2 Pair (reify (codeF1 g)) xT))))
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp I I))))
                              (ap2 Pair (reify (codeF1 f))
                                        (reify (codeF1 g))))
                    xT))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 f))
            (ap2 Pair (reify tagAp1)
              (ap2 Pair (reify (codeF1 g)) xT)))))))
  thmTDispAxComp_param f g xT =
    let payT = ap2 Pair (reify (codeF1 f)) (ap2 Pair (reify (codeF1 g)) xT)
        a   = ap2 Pair tagCode_axComp payT
        b   = ap2 Pair (ap1 thmT tagCode_axComp) (ap1 thmT payT)
        e1  = dispatchOpens tagAxConst payT
        s1  = skipAtTag (natCode tagAxI)     tagCode_axComp payT b body_axI     next_axI
                 (teqDiff tagAxI     tagAxComp refl)
        s2  = skipAtTag (natCode tagAxFst)   tagCode_axComp payT b body_axFst   next_axFst
                 (teqDiff tagAxFst   tagAxComp refl)
        s3  = skipAtTag (natCode tagAxSnd)   tagCode_axComp payT b body_axSnd   next_axSnd
                 (teqDiff tagAxSnd   tagAxComp refl)
        s4  = skipAtTag (natCode tagAxConst) tagCode_axComp payT b body_axConst next_axConst
                 (teqDiff tagAxConst tagAxComp refl)
        h   = hitAtTag  (natCode tagAxComp)  tagCode_axComp payT b body_axComp  next_axComp
                 (teqEq tagAxComp)
        be  = body_axComp_eval_param f g xT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans h be)))))

  body_axComp2_eval : (h' : Fun2) (f g : Fun1) (t bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axComp2
            (ap2 Pair tagCode_axComp2
              (reify (nd (codeF2 h') (nd (codeF1 f) (nd (codeF1 g) (code t)))))) bb)
      (reify (outAxComp2 h' f g t))))
  body_axComp2_eval h' f g t bb =
    let ch    = reify (codeF2 h')
        cf    = reify (codeF1 f)
        cg    = reify (codeF1 g)
        ct    = reify (code t)
        payT  = ap2 Pair ch (ap2 Pair cf (ap2 Pair cg ct))
        a     = ap2 Pair tagCode_axComp2 payT
        K_a1V = tagAp1
        K_a1  = reify K_a1V
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_c2V = leftT (codeF1 (Comp2 IfLf I I))
        K_c2  = reify K_c2V
        ext_ch = liftCompFstSnd_evalPair tagCode_axComp2 ch (ap2 Pair cf (ap2 Pair cg ct)) bb
        ext_cf = liftFstSndSnd_evalPair3 tagCode_axComp2 ch cf (ap2 Pair cg ct) bb
        ext_cg = liftFstSndSndSnd_evalPair4 tagCode_axComp2 ch cf cg ct bb
        ext_ct = liftSndSndSndSnd_evalPair4 tagCode_axComp2 ch cf cg ct bb
        -- LHS = Pair K_a1 (Pair (Pair K_c2 (Pair ch (Pair cf cg))) ct)
        cfcg = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                 a bb cf cg ext_cf ext_cg
        chCfcg = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb ch (ap2 Pair cf cg) ext_ch cfcg
        kc2 = pairOfConst_eval K_c2V
                (Fan (Lift (Comp Fst Snd))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair) Pair)
                a bb (ap2 Pair ch (ap2 Pair cf cg)) chCfcg
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_c2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   a bb (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) ct
                   kc2 ext_ct
        lhsBuild = pairOfConst_eval K_a1V
                     (Fan (Fan (Lift (KT K_c2))
                               (Fan (Lift (Comp Fst Snd))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) ct)
                     midLHS
        -- RHS = Pair K_a2 (Pair ch (Pair (Pair K_a1 (Pair cf ct)) (Pair K_a1 (Pair cg ct))))
        cfct = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                 a bb cf ct ext_cf ext_ct
        cgct = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                 a bb cg ct ext_cg ext_ct
        ka1Cfct = pairOfConst_eval K_a1V
                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                    a bb (ap2 Pair cf ct) cfct
        ka1Cgct = pairOfConst_eval K_a1V
                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                    a bb (ap2 Pair cg ct) cgct
        innerRHS = pairOfFan_eval
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb
                     (ap2 Pair K_a1 (ap2 Pair cf ct))
                     (ap2 Pair K_a1 (ap2 Pair cg ct))
                     ka1Cfct ka1Cgct
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     Pair)
                   a bb ch
                   (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf ct))
                              (ap2 Pair K_a1 (ap2 Pair cg ct)))
                   ext_ch innerRHS
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan
                            (Fan (Lift (KT K_a1))
                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair)
                            (Fan (Lift (KT K_a1))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair)
                            Pair)
                          Pair)
                     a bb
                     (ap2 Pair ch (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf ct))
                                              (ap2 Pair K_a1 (ap2 Pair cg ct))))
                     midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_c2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) ct))
         (ap2 Pair K_a2 (ap2 Pair ch (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf ct))
                                                (ap2 Pair K_a1 (ap2 Pair cg ct)))))
         lhsBuild rhsBuild

  thmTDispAxComp2 : (h' : Fun2) (f g : Fun1) (t : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxComp2 h' f g t)))
                       (reify (outAxComp2 h' f g t))))
  thmTDispAxComp2 h' f g t =
    let payT = reify (nd (codeF2 h') (nd (codeF1 f) (nd (codeF1 g) (code t))))
        a   = ap2 Pair tagCode_axComp2 payT
        b   = ap2 Pair (ap1 thmT tagCode_axComp2) (ap1 thmT payT)
        e1  = dispatchOpens tagAxComp payT
        s1  = skipAtTag (natCode tagAxI)     tagCode_axComp2 payT b body_axI     next_axI
                 (teqDiff tagAxI     tagAxComp2 refl)
        s2  = skipAtTag (natCode tagAxFst)   tagCode_axComp2 payT b body_axFst   next_axFst
                 (teqDiff tagAxFst   tagAxComp2 refl)
        s3  = skipAtTag (natCode tagAxSnd)   tagCode_axComp2 payT b body_axSnd   next_axSnd
                 (teqDiff tagAxSnd   tagAxComp2 refl)
        s4  = skipAtTag (natCode tagAxConst) tagCode_axComp2 payT b body_axConst next_axConst
                 (teqDiff tagAxConst tagAxComp2 refl)
        s5  = skipAtTag (natCode tagAxComp)  tagCode_axComp2 payT b body_axComp  next_axComp
                 (teqDiff tagAxComp  tagAxComp2 refl)
        hh  = hitAtTag  (natCode tagAxComp2) tagCode_axComp2 payT b body_axComp2 next_axComp2
                 (teqEq tagAxComp2)
        be  = body_axComp2_eval h' f g t b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans hh be))))))

  -- Parametric variant of body_axComp2_eval (Theorem 12 / Parts/Comp2.agda).
  body_axComp2_eval_param : (h' : Fun2) (f g : Fun1) (xT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axComp2
            (ap2 Pair tagCode_axComp2
              (ap2 Pair (reify (codeF2 h'))
                (ap2 Pair (reify (codeF1 f))
                  (ap2 Pair (reify (codeF1 g)) xT)))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp2 IfLf I I))))
                              (ap2 Pair (reify (codeF2 h'))
                                (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))))
                    xT))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 h'))
            (ap2 Pair (ap2 Pair (reify tagAp1)
                                (ap2 Pair (reify (codeF1 f)) xT))
                      (ap2 Pair (reify tagAp1)
                                (ap2 Pair (reify (codeF1 g)) xT))))))))
  body_axComp2_eval_param h' f g xT bb =
    let ch    = reify (codeF2 h')
        cf    = reify (codeF1 f)
        cg    = reify (codeF1 g)
        payT  = ap2 Pair ch (ap2 Pair cf (ap2 Pair cg xT))
        a     = ap2 Pair tagCode_axComp2 payT
        K_a1V = tagAp1
        K_a1  = reify K_a1V
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_c2V = leftT (codeF1 (Comp2 IfLf I I))
        K_c2  = reify K_c2V
        ext_ch = liftCompFstSnd_evalPair tagCode_axComp2 ch (ap2 Pair cf (ap2 Pair cg xT)) bb
        ext_cf = liftFstSndSnd_evalPair3 tagCode_axComp2 ch cf (ap2 Pair cg xT) bb
        ext_cg = liftFstSndSndSnd_evalPair4 tagCode_axComp2 ch cf cg xT bb
        ext_xT = liftSndSndSndSnd_evalPair4 tagCode_axComp2 ch cf cg xT bb
        cfcg = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                 a bb cf cg ext_cf ext_cg
        chCfcg = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb ch (ap2 Pair cf cg) ext_ch cfcg
        kc2 = pairOfConst_eval K_c2V
                (Fan (Lift (Comp Fst Snd))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair) Pair)
                a bb (ap2 Pair ch (ap2 Pair cf cg)) chCfcg
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_c2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   a bb (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) xT
                   kc2 ext_xT
        lhsBuild = pairOfConst_eval K_a1V
                     (Fan (Fan (Lift (KT K_c2))
                               (Fan (Lift (Comp Fst Snd))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) xT)
                     midLHS
        cfxT = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                 a bb cf xT ext_cf ext_xT
        cgxT = pairOfFan_eval
                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                 a bb cg xT ext_cg ext_xT
        ka1Cfxt = pairOfConst_eval K_a1V
                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                    a bb (ap2 Pair cf xT) cfxT
        ka1Cgxt = pairOfConst_eval K_a1V
                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                    a bb (ap2 Pair cg xT) cgxT
        innerRHS = pairOfFan_eval
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb
                     (ap2 Pair K_a1 (ap2 Pair cf xT))
                     (ap2 Pair K_a1 (ap2 Pair cg xT))
                     ka1Cfxt ka1Cgxt
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Fan
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     Pair)
                   a bb ch
                   (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf xT))
                              (ap2 Pair K_a1 (ap2 Pair cg xT)))
                   ext_ch innerRHS
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan
                            (Fan (Lift (KT K_a1))
                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair)
                            (Fan (Lift (KT K_a1))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair)
                            Pair)
                          Pair)
                     a bb
                     (ap2 Pair ch (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf xT))
                                              (ap2 Pair K_a1 (ap2 Pair cg xT))))
                     midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_c2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_c2 (ap2 Pair ch (ap2 Pair cf cg))) xT))
         (ap2 Pair K_a2 (ap2 Pair ch (ap2 Pair (ap2 Pair K_a1 (ap2 Pair cf xT))
                                                (ap2 Pair K_a1 (ap2 Pair cg xT)))))
         lhsBuild rhsBuild

  -- Parametric variant of thmTDispAxComp2.
  thmTDispAxComp2_param : (h' : Fun2) (f g : Fun1) (xT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axComp2
                          (ap2 Pair (reify (codeF2 h'))
                            (ap2 Pair (reify (codeF1 f))
                              (ap2 Pair (reify (codeF1 g)) xT)))))
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Comp2 IfLf I I))))
                              (ap2 Pair (reify (codeF2 h'))
                                (ap2 Pair (reify (codeF1 f)) (reify (codeF1 g)))))
                    xT))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 h'))
            (ap2 Pair (ap2 Pair (reify tagAp1)
                                (ap2 Pair (reify (codeF1 f)) xT))
                      (ap2 Pair (reify tagAp1)
                                (ap2 Pair (reify (codeF1 g)) xT))))))))
  thmTDispAxComp2_param h' f g xT =
    let payT = ap2 Pair (reify (codeF2 h'))
                  (ap2 Pair (reify (codeF1 f))
                    (ap2 Pair (reify (codeF1 g)) xT))
        a   = ap2 Pair tagCode_axComp2 payT
        b   = ap2 Pair (ap1 thmT tagCode_axComp2) (ap1 thmT payT)
        e1  = dispatchOpens tagAxComp payT
        s1  = skipAtTag (natCode tagAxI)     tagCode_axComp2 payT b body_axI     next_axI
                 (teqDiff tagAxI     tagAxComp2 refl)
        s2  = skipAtTag (natCode tagAxFst)   tagCode_axComp2 payT b body_axFst   next_axFst
                 (teqDiff tagAxFst   tagAxComp2 refl)
        s3  = skipAtTag (natCode tagAxSnd)   tagCode_axComp2 payT b body_axSnd   next_axSnd
                 (teqDiff tagAxSnd   tagAxComp2 refl)
        s4  = skipAtTag (natCode tagAxConst) tagCode_axComp2 payT b body_axConst next_axConst
                 (teqDiff tagAxConst tagAxComp2 refl)
        s5  = skipAtTag (natCode tagAxComp)  tagCode_axComp2 payT b body_axComp  next_axComp
                 (teqDiff tagAxComp  tagAxComp2 refl)
        hh  = hitAtTag  (natCode tagAxComp2) tagCode_axComp2 payT b body_axComp2 next_axComp2
                 (teqEq tagAxComp2)
        be  = body_axComp2_eval_param h' f g xT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans hh be))))))

  body_axLift_eval : (f : Fun1) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axLift
            (ap2 Pair tagCode_axLift
                       (reify (nd (codeF1 f) (nd (code a') (code b'))))) bb)
      (reify (outAxLift f a' b'))))
  body_axLift_eval f a' b' bb =
    let cf    = reify (codeF1 f)
        payAT = reify (code a')
        payBT = reify (code b')
        payT  = ap2 Pair cf (ap2 Pair payAT payBT)
        a     = ap2 Pair tagCode_axLift payT
        K1V   = tagAp2
        K2V   = leftT (codeF2 (Lift I))
        K3V   = tagAp1
        K1    = reify K1V
        K2    = reify K2V
        K3    = reify K3V
        ext_cf    = liftCompFstSnd_evalPair tagCode_axLift cf (ap2 Pair payAT payBT) bb
        ext_payAT = liftFstSndSnd_evalPair3 tagCode_axLift cf payAT payBT bb
        ext_payBT = liftSndSndSnd_evalPair3 tagCode_axLift cf payAT payBT bb
        -- LHS: Pair K1 (Pair (Pair K2 cf) (Pair payAT payBT))
        kLiftCf = pairOfConst_eval K2V (Lift (Comp Fst Snd)) a bb cf ext_cf
        payATBT = pairOfFan_eval
                    (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb
                    payAT payBT ext_payAT ext_payBT
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb
                   (ap2 Pair K2 cf) (ap2 Pair payAT payBT)
                   kLiftCf payATBT
        lhsBuild = pairOfConst_eval K1V
                     (Fan (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K2 cf) (ap2 Pair payAT payBT))
                     midLHS
        -- RHS: Pair K3 (Pair cf payAT)
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd)))
                   a bb cf payAT ext_cf ext_payAT
        rhsBuild = pairOfConst_eval K3V
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair cf payAT) midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
              Pair)
         (Fan (Lift (KT K3))
              (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
              Pair)
         a bb
         (ap2 Pair K1 (ap2 Pair (ap2 Pair K2 cf) (ap2 Pair payAT payBT)))
         (ap2 Pair K3 (ap2 Pair cf payAT))
         lhsBuild rhsBuild

  thmTDispAxLift : (f : Fun1) (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxLift f a' b')))
                       (reify (outAxLift f a' b'))))
  thmTDispAxLift f a' b' =
    let payT = reify (nd (codeF1 f) (nd (code a') (code b')))
        a   = ap2 Pair tagCode_axLift payT
        b   = ap2 Pair (ap1 thmT tagCode_axLift) (ap1 thmT payT)
        e1  = dispatchOpens tagAxComp2 payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axLift payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxLift refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axLift payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxLift refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axLift payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxLift refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axLift payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxLift refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axLift payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxLift refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axLift payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxLift refl)
        hh  = hitAtTag  (natCode tagAxLift)   tagCode_axLift payT b body_axLift   next_axLift
                 (teqEq tagAxLift)
        be  = body_axLift_eval f a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans hh be)))))))

  -- Parametric variant of body_axLift_eval (Theorem 12 / Parts/Lift.agda).
  body_axLift_eval_param : (f : Fun1) (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axLift
            (ap2 Pair tagCode_axLift
                       (ap2 Pair (reify (codeF1 f)) (ap2 Pair aT bT))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Lift I))))
                              (reify (codeF1 f)))
                    (ap2 Pair aT bT)))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 f)) aT)))))
  body_axLift_eval_param f aT bT bb =
    let cf    = reify (codeF1 f)
        payT  = ap2 Pair cf (ap2 Pair aT bT)
        a     = ap2 Pair tagCode_axLift payT
        K1V   = tagAp2
        K2V   = leftT (codeF2 (Lift I))
        K3V   = tagAp1
        K1    = reify K1V
        K2    = reify K2V
        K3    = reify K3V
        ext_cf    = liftCompFstSnd_evalPair tagCode_axLift cf (ap2 Pair aT bT) bb
        ext_aT    = liftFstSndSnd_evalPair3 tagCode_axLift cf aT bT bb
        ext_bT    = liftSndSndSnd_evalPair3 tagCode_axLift cf aT bT bb
        kLiftCf = pairOfConst_eval K2V (Lift (Comp Fst Snd)) a bb cf ext_cf
        payATBT = pairOfFan_eval
                    (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb
                    aT bT ext_aT ext_bT
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb
                   (ap2 Pair K2 cf) (ap2 Pair aT bT)
                   kLiftCf payATBT
        lhsBuild = pairOfConst_eval K1V
                     (Fan (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K2 cf) (ap2 Pair aT bT))
                     midLHS
        midRHS = pairOfFan_eval
                   (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd)))
                   a bb cf aT ext_cf ext_aT
        rhsBuild = pairOfConst_eval K3V
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair cf aT) midRHS
    in pairOfFan_eval
         (Fan (Lift (KT K1))
              (Fan (Fan (Lift (KT K2)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
              Pair)
         (Fan (Lift (KT K3))
              (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
              Pair)
         a bb
         (ap2 Pair K1 (ap2 Pair (ap2 Pair K2 cf) (ap2 Pair aT bT)))
         (ap2 Pair K3 (ap2 Pair cf aT))
         lhsBuild rhsBuild

  -- Parametric variant of thmTDispAxLift.
  thmTDispAxLift_param : (f : Fun1) (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axLift
                          (ap2 Pair (reify (codeF1 f)) (ap2 Pair aT bT))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Lift I))))
                              (reify (codeF1 f)))
                    (ap2 Pair aT bT)))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 f)) aT)))))
  thmTDispAxLift_param f aT bT =
    let payT = ap2 Pair (reify (codeF1 f)) (ap2 Pair aT bT)
        a   = ap2 Pair tagCode_axLift payT
        b   = ap2 Pair (ap1 thmT tagCode_axLift) (ap1 thmT payT)
        e1  = dispatchOpens tagAxComp2 payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axLift payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxLift refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axLift payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxLift refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axLift payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxLift refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axLift payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxLift refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axLift payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxLift refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axLift payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxLift refl)
        hh  = hitAtTag  (natCode tagAxLift)   tagCode_axLift payT b body_axLift   next_axLift
                 (teqEq tagAxLift)
        be  = body_axLift_eval_param f aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans hh be)))))))

  body_axPost_eval : (f : Fun1) (h' : Fun2) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axPost
            (ap2 Pair tagCode_axPost
              (reify (nd (codeF1 f) (nd (codeF2 h') (nd (code a') (code b')))))) bb)
      (reify (outAxPost f h' a' b'))))
  body_axPost_eval f h' a' b' bb =
    let cf    = reify (codeF1 f)
        ch    = reify (codeF2 h')
        payAT = reify (code a')
        payBT = reify (code b')
        payT  = ap2 Pair cf (ap2 Pair ch (ap2 Pair payAT payBT))
        a     = ap2 Pair tagCode_axPost payT
        K_a1V = tagAp1
        K_a1  = reify K_a1V
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_pV  = leftT (codeF2 (Post I IfLf))
        K_p   = reify K_pV
        ext_cf    = liftCompFstSnd_evalPair tagCode_axPost cf
                       (ap2 Pair ch (ap2 Pair payAT payBT)) bb
        ext_ch    = liftFstSndSnd_evalPair3 tagCode_axPost cf ch
                       (ap2 Pair payAT payBT) bb
        ext_payAT = liftFstSndSndSnd_evalPair4 tagCode_axPost cf ch payAT payBT bb
        ext_payBT = liftSndSndSndSnd_evalPair4 tagCode_axPost cf ch payAT payBT bb
        -- LHS: Pair K_a2 (Pair (Pair K_p (Pair cf ch)) (Pair payAT payBT))
        cfch = pairOfFan_eval
                 (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd Snd))) a bb cf ch ext_cf ext_ch
        kpCfch = pairOfConst_eval K_pV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair cf ch) cfch
        pATpBT = pairOfFan_eval
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   a bb payAT payBT ext_payAT ext_payBT
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_p))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                        Pair)
                   a bb
                   (ap2 Pair K_p (ap2 Pair cf ch))
                   (ap2 Pair payAT payBT)
                   kpCfch pATpBT
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_p))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair)
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_p (ap2 Pair cf ch))
                                (ap2 Pair payAT payBT))
                     midLHS
        -- RHS: Pair K_a1 (Pair cf (Pair K_a2 (Pair ch (Pair payAT payBT))))
        chPATpBT = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd Snd)))
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                          Pair)
                     a bb ch (ap2 Pair payAT payBT) ext_ch pATpBT
        ka2chPATpBT = pairOfConst_eval K_a2V
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair)
                        a bb (ap2 Pair ch (ap2 Pair payAT payBT)) chPATpBT
        cfKa2 = pairOfFan_eval
                  (Lift (Comp Fst Snd))
                  (Fan (Lift (KT K_a2))
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 Pair) Pair) Pair)
                  a bb cf
                  (ap2 Pair K_a2 (ap2 Pair ch (ap2 Pair payAT payBT)))
                  ext_cf ka2chPATpBT
        rhsBuild = pairOfConst_eval K_a1V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair cf (ap2 Pair K_a2
                                      (ap2 Pair ch (ap2 Pair payAT payBT))))
                     cfKa2
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_p))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                        Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_p (ap2 Pair cf ch))
                                    (ap2 Pair payAT payBT)))
         (ap2 Pair K_a1 (ap2 Pair cf
                           (ap2 Pair K_a2
                              (ap2 Pair ch (ap2 Pair payAT payBT)))))
         lhsBuild rhsBuild

  thmTDispAxPost : (f : Fun1) (h' : Fun2) (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxPost f h' a' b')))
                       (reify (outAxPost f h' a' b'))))
  thmTDispAxPost f h' a' b' =
    let payT = reify (nd (codeF1 f) (nd (codeF2 h') (nd (code a') (code b'))))
        a   = ap2 Pair tagCode_axPost payT
        b   = ap2 Pair (ap1 thmT tagCode_axPost) (ap1 thmT payT)
        e1  = dispatchOpens tagAxLift payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axPost payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxPost refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axPost payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxPost refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axPost payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxPost refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axPost payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxPost refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axPost payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxPost refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axPost payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxPost refl)
        s7  = skipAtTag (natCode tagAxLift)   tagCode_axPost payT b body_axLift   next_axLift
                 (teqDiff tagAxLift   tagAxPost refl)
        hh  = hitAtTag  (natCode tagAxPost)   tagCode_axPost payT b body_axPost   next_axPost
                 (teqEq tagAxPost)
        be  = body_axPost_eval f h' a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans hh be))))))))

  -- Parametric variant of body_axPost_eval (Theorem 12 / Parts/Post.agda).
  body_axPost_eval_param : (f : Fun1) (h' : Fun2) (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axPost
            (ap2 Pair tagCode_axPost
              (ap2 Pair (reify (codeF1 f))
                (ap2 Pair (reify (codeF2 h'))
                  (ap2 Pair aT bT)))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Post I IfLf))))
                              (ap2 Pair (reify (codeF1 f))
                                        (reify (codeF2 h'))))
                    (ap2 Pair aT bT)))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 f))
            (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 h'))
                (ap2 Pair aT bT))))))))
  body_axPost_eval_param f h' aT bT bb =
    let cf    = reify (codeF1 f)
        ch    = reify (codeF2 h')
        payT  = ap2 Pair cf (ap2 Pair ch (ap2 Pair aT bT))
        a     = ap2 Pair tagCode_axPost payT
        K_a1V = tagAp1
        K_a1  = reify K_a1V
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_pV  = leftT (codeF2 (Post I IfLf))
        K_p   = reify K_pV
        ext_cf    = liftCompFstSnd_evalPair tagCode_axPost cf
                       (ap2 Pair ch (ap2 Pair aT bT)) bb
        ext_ch    = liftFstSndSnd_evalPair3 tagCode_axPost cf ch
                       (ap2 Pair aT bT) bb
        ext_aT    = liftFstSndSndSnd_evalPair4 tagCode_axPost cf ch aT bT bb
        ext_bT    = liftSndSndSndSnd_evalPair4 tagCode_axPost cf ch aT bT bb
        cfch = pairOfFan_eval
                 (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd Snd))) a bb cf ch ext_cf ext_ch
        kpCfch = pairOfConst_eval K_pV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair cf ch) cfch
        pATpBT = pairOfFan_eval
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                   a bb aT bT ext_aT ext_bT
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_p))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                        Pair)
                   a bb
                   (ap2 Pair K_p (ap2 Pair cf ch))
                   (ap2 Pair aT bT)
                   kpCfch pATpBT
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_p))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair)
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_p (ap2 Pair cf ch))
                                (ap2 Pair aT bT))
                     midLHS
        chPATpBT = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd Snd)))
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                          Pair)
                     a bb ch (ap2 Pair aT bT) ext_ch pATpBT
        ka2chPATpBT = pairOfConst_eval K_a2V
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair)
                        a bb (ap2 Pair ch (ap2 Pair aT bT)) chPATpBT
        cfKa2 = pairOfFan_eval
                  (Lift (Comp Fst Snd))
                  (Fan (Lift (KT K_a2))
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                 Pair) Pair) Pair)
                  a bb cf
                  (ap2 Pair K_a2 (ap2 Pair ch (ap2 Pair aT bT)))
                  ext_cf ka2chPATpBT
        rhsBuild = pairOfConst_eval K_a1V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair cf (ap2 Pair K_a2
                                      (ap2 Pair ch (ap2 Pair aT bT))))
                     cfKa2
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_p))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                        Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_p (ap2 Pair cf ch))
                                    (ap2 Pair aT bT)))
         (ap2 Pair K_a1 (ap2 Pair cf
                           (ap2 Pair K_a2
                              (ap2 Pair ch (ap2 Pair aT bT)))))
         lhsBuild rhsBuild

  -- Parametric variant of thmTDispAxPost.
  thmTDispAxPost_param : (f : Fun1) (h' : Fun2) (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axPost
                    (ap2 Pair (reify (codeF1 f))
                      (ap2 Pair (reify (codeF2 h'))
                        (ap2 Pair aT bT)))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Post I IfLf))))
                              (ap2 Pair (reify (codeF1 f))
                                        (reify (codeF2 h'))))
                    (ap2 Pair aT bT)))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (reify (codeF1 f))
            (ap2 Pair (reify tagAp2)
              (ap2 Pair (reify (codeF2 h'))
                (ap2 Pair aT bT))))))))
  thmTDispAxPost_param f h' aT bT =
    let payT = ap2 Pair (reify (codeF1 f))
                 (ap2 Pair (reify (codeF2 h')) (ap2 Pair aT bT))
        a   = ap2 Pair tagCode_axPost payT
        b   = ap2 Pair (ap1 thmT tagCode_axPost) (ap1 thmT payT)
        e1  = dispatchOpens tagAxLift payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axPost payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxPost refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axPost payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxPost refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axPost payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxPost refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axPost payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxPost refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axPost payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxPost refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axPost payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxPost refl)
        s7  = skipAtTag (natCode tagAxLift)   tagCode_axPost payT b body_axLift   next_axLift
                 (teqDiff tagAxLift   tagAxPost refl)
        hh  = hitAtTag  (natCode tagAxPost)   tagCode_axPost payT b body_axPost   next_axPost
                 (teqEq tagAxPost)
        be  = body_axPost_eval_param f h' aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans hh be))))))))

  body_axFan_eval : (h1' h2' h' : Fun2) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFan
            (ap2 Pair tagCode_axFan
              (reify (nd (codeF2 h1')
                          (nd (codeF2 h2')
                              (nd (codeF2 h') (nd (code a') (code b'))))))) bb)
      (reify (outAxFan h1' h2' h' a' b'))))
  body_axFan_eval h1' h2' h' a' b' bb =
    let ch1   = reify (codeF2 h1')
        ch2   = reify (codeF2 h2')
        ch    = reify (codeF2 h')
        payAT = reify (code a')
        payBT = reify (code b')
        payT  = ap2 Pair ch1 (ap2 Pair ch2 (ap2 Pair ch (ap2 Pair payAT payBT)))
        a     = ap2 Pair tagCode_axFan payT
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_fV  = leftT (codeF2 (Fan IfLf IfLf IfLf))
        K_f   = reify K_fV
        ext_ch1   = liftCompFstSnd_evalPair tagCode_axFan ch1
                       (ap2 Pair ch2 (ap2 Pair ch (ap2 Pair payAT payBT))) bb
        ext_ch2   = liftFstSndSnd_evalPair3 tagCode_axFan ch1 ch2
                       (ap2 Pair ch (ap2 Pair payAT payBT)) bb
        ext_ch    = liftFstSndSndSnd_evalPair4 tagCode_axFan ch1 ch2 ch
                       (ap2 Pair payAT payBT) bb
        ext_payAT = liftFstSndSndSndSnd_evalPair5 tagCode_axFan ch1 ch2 ch payAT payBT bb
        ext_payBT = liftSndSndSndSndSnd_evalPair5 tagCode_axFan ch1 ch2 ch payAT payBT bb
        -- Re-usable: payATBT = Pair payAT payBT.
        payATBT = pairOfFan_eval
                    (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    a bb payAT payBT ext_payAT ext_payBT
        -- LHS: Pair K_a2 (Pair (Pair K_f (Pair ch1 (Pair ch2 ch))) (Pair payAT payBT))
        ch2ch = pairOfFan_eval
                  (Lift (Comp Fst (Comp Snd Snd)))
                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                  a bb ch2 ch ext_ch2 ext_ch
        ch1ch2ch = pairOfFan_eval
                     (Lift (Comp Fst Snd))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb ch1 (ap2 Pair ch2 ch) ext_ch1 ch2ch
        kfChain = pairOfConst_eval K_fV
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                         Pair)
                    a bb (ap2 Pair ch1 (ap2 Pair ch2 ch)) ch1ch2ch
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_f))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        Pair)
                   a bb
                   (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                   (ap2 Pair payAT payBT)
                   kfChain payATBT
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_f))
                               (Fan (Lift (Comp Fst Snd))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                                (ap2 Pair payAT payBT))
                     midLHS
        -- RHS: Pair K_a2 (Pair ch (Pair LHSh1 LHSh2)) where
        --   LHSh1 = Pair K_a2 (Pair ch1 (Pair payAT payBT))
        --   LHSh2 = Pair K_a2 (Pair ch2 (Pair payAT payBT))
        ch1pATpBT = pairOfFan_eval
                      (Lift (Comp Fst Snd))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           Pair)
                      a bb ch1 (ap2 Pair payAT payBT) ext_ch1 payATBT
        ch2pATpBT = pairOfFan_eval
                      (Lift (Comp Fst (Comp Snd Snd)))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           Pair)
                      a bb ch2 (ap2 Pair payAT payBT) ext_ch2 payATBT
        ka2ch1pATpBT = pairOfConst_eval K_a2V
                         (Fan (Lift (Comp Fst Snd))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair)
                         a bb (ap2 Pair ch1 (ap2 Pair payAT payBT)) ch1pATpBT
        ka2ch2pATpBT = pairOfConst_eval K_a2V
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair)
                         a bb (ap2 Pair ch2 (ap2 Pair payAT payBT)) ch2pATpBT
        twoLHSs = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (Comp Fst Snd))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                    (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT)))
                    ka2ch1pATpBT ka2ch2pATpBT
        chLHSs = pairOfFan_eval
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst Snd))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair) Pair)
                   a bb ch
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                              (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT))))
                   ext_ch twoLHSs
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (Comp Fst Snd))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair) Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair ch
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                                  (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT)))))
                     chLHSs
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_f))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst Snd))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair) Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                                    (ap2 Pair payAT payBT)))
         (ap2 Pair K_a2 (ap2 Pair ch
                           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair payAT payBT)))
                                      (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair payAT payBT))))))
         lhsBuild rhsBuild

  thmTDispAxFan : (h1' h2' h' : Fun2) (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxFan h1' h2' h' a' b')))
                       (reify (outAxFan h1' h2' h' a' b'))))
  thmTDispAxFan h1' h2' h' a' b' =
    let payT = reify (nd (codeF2 h1')
                          (nd (codeF2 h2')
                              (nd (codeF2 h') (nd (code a') (code b')))))
        a   = ap2 Pair tagCode_axFan payT
        b   = ap2 Pair (ap1 thmT tagCode_axFan) (ap1 thmT payT)
        e1  = dispatchOpens tagAxPost payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axFan payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxFan refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axFan payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxFan refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axFan payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxFan refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axFan payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxFan refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axFan payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxFan refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axFan payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxFan refl)
        s7  = skipAtTag (natCode tagAxLift)   tagCode_axFan payT b body_axLift   next_axLift
                 (teqDiff tagAxLift   tagAxFan refl)
        s8  = skipAtTag (natCode tagAxPost)   tagCode_axFan payT b body_axPost   next_axPost
                 (teqDiff tagAxPost   tagAxFan refl)
        hh  = hitAtTag  (natCode tagAxFan)    tagCode_axFan payT b body_axFan    next_axFan
                 (teqEq tagAxFan)
        be  = body_axFan_eval h1' h2' h' a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans hh be)))))))))

  -- Parametric variant of body_axFan_eval (Theorem 12 / Parts/Fan.agda).
  body_axFan_eval_param : (h1' h2' h' : Fun2) (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFan
            (ap2 Pair tagCode_axFan
              (ap2 Pair (reify (codeF2 h1'))
                (ap2 Pair (reify (codeF2 h2'))
                  (ap2 Pair (reify (codeF2 h'))
                    (ap2 Pair aT bT))))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Fan IfLf IfLf IfLf))))
                              (ap2 Pair (reify (codeF2 h1'))
                                (ap2 Pair (reify (codeF2 h2'))
                                  (reify (codeF2 h')))))
                    (ap2 Pair aT bT)))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 h'))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 h1')) (ap2 Pair aT bT)))
                      (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 h2')) (ap2 Pair aT bT)))))))))
  body_axFan_eval_param h1' h2' h' aT bT bb =
    let ch1   = reify (codeF2 h1')
        ch2   = reify (codeF2 h2')
        ch    = reify (codeF2 h')
        payT  = ap2 Pair ch1 (ap2 Pair ch2 (ap2 Pair ch (ap2 Pair aT bT)))
        a     = ap2 Pair tagCode_axFan payT
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_fV  = leftT (codeF2 (Fan IfLf IfLf IfLf))
        K_f   = reify K_fV
        ext_ch1   = liftCompFstSnd_evalPair tagCode_axFan ch1
                       (ap2 Pair ch2 (ap2 Pair ch (ap2 Pair aT bT))) bb
        ext_ch2   = liftFstSndSnd_evalPair3 tagCode_axFan ch1 ch2
                       (ap2 Pair ch (ap2 Pair aT bT)) bb
        ext_ch    = liftFstSndSndSnd_evalPair4 tagCode_axFan ch1 ch2 ch
                       (ap2 Pair aT bT) bb
        ext_aT    = liftFstSndSndSndSnd_evalPair5 tagCode_axFan ch1 ch2 ch aT bT bb
        ext_bT    = liftSndSndSndSndSnd_evalPair5 tagCode_axFan ch1 ch2 ch aT bT bb
        payATBT = pairOfFan_eval
                    (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    a bb aT bT ext_aT ext_bT
        ch2ch = pairOfFan_eval
                  (Lift (Comp Fst (Comp Snd Snd)))
                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                  a bb ch2 ch ext_ch2 ext_ch
        ch1ch2ch = pairOfFan_eval
                     (Lift (Comp Fst Snd))
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb ch1 (ap2 Pair ch2 ch) ext_ch1 ch2ch
        kfChain = pairOfConst_eval K_fV
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                         Pair)
                    a bb (ap2 Pair ch1 (ap2 Pair ch2 ch)) ch1ch2ch
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_f))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        Pair)
                   a bb
                   (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                   (ap2 Pair aT bT)
                   kfChain payATBT
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_f))
                               (Fan (Lift (Comp Fst Snd))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                               Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                                (ap2 Pair aT bT))
                     midLHS
        ch1pATpBT = pairOfFan_eval
                      (Lift (Comp Fst Snd))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           Pair)
                      a bb ch1 (ap2 Pair aT bT) ext_ch1 payATBT
        ch2pATpBT = pairOfFan_eval
                      (Lift (Comp Fst (Comp Snd Snd)))
                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                           Pair)
                      a bb ch2 (ap2 Pair aT bT) ext_ch2 payATBT
        ka2ch1pATpBT = pairOfConst_eval K_a2V
                         (Fan (Lift (Comp Fst Snd))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair)
                         a bb (ap2 Pair ch1 (ap2 Pair aT bT)) ch1pATpBT
        ka2ch2pATpBT = pairOfConst_eval K_a2V
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair)
                         a bb (ap2 Pair ch2 (ap2 Pair aT bT)) ch2pATpBT
        twoLHSs = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (Comp Fst Snd))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                   Pair) Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair aT bT)))
                    (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair aT bT)))
                    ka2ch1pATpBT ka2ch2pATpBT
        chLHSs = pairOfFan_eval
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst Snd))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair) Pair)
                   a bb ch
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair aT bT)))
                              (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair aT bT))))
                   ext_ch twoLHSs
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (Comp Fst Snd))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                              Pair) Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair ch
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair aT bT)))
                                  (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair aT bT)))))
                     chLHSs
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_f))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                        Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst Snd))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                       Pair) Pair) Pair) Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_f (ap2 Pair ch1 (ap2 Pair ch2 ch)))
                                    (ap2 Pair aT bT)))
         (ap2 Pair K_a2 (ap2 Pair ch
                           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair ch1 (ap2 Pair aT bT)))
                                      (ap2 Pair K_a2 (ap2 Pair ch2 (ap2 Pair aT bT))))))
         lhsBuild rhsBuild

  -- Parametric variant of thmTDispAxFan.
  thmTDispAxFan_param : (h1' h2' h' : Fun2) (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axFan
                          (ap2 Pair (reify (codeF2 h1'))
                            (ap2 Pair (reify (codeF2 h2'))
                              (ap2 Pair (reify (codeF2 h'))
                                (ap2 Pair aT bT))))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (Fan IfLf IfLf IfLf))))
                              (ap2 Pair (reify (codeF2 h1'))
                                (ap2 Pair (reify (codeF2 h2'))
                                  (reify (codeF2 h')))))
                    (ap2 Pair aT bT)))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 h'))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 h1')) (ap2 Pair aT bT)))
                      (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 h2')) (ap2 Pair aT bT)))))))))
  thmTDispAxFan_param h1' h2' h' aT bT =
    let payT = ap2 Pair (reify (codeF2 h1'))
                  (ap2 Pair (reify (codeF2 h2'))
                    (ap2 Pair (reify (codeF2 h'))
                      (ap2 Pair aT bT)))
        a   = ap2 Pair tagCode_axFan payT
        b   = ap2 Pair (ap1 thmT tagCode_axFan) (ap1 thmT payT)
        e1  = dispatchOpens tagAxPost payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axFan payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxFan refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axFan payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxFan refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axFan payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxFan refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axFan payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxFan refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axFan payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxFan refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axFan payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxFan refl)
        s7  = skipAtTag (natCode tagAxLift)   tagCode_axFan payT b body_axLift   next_axLift
                 (teqDiff tagAxLift   tagAxFan refl)
        s8  = skipAtTag (natCode tagAxPost)   tagCode_axFan payT b body_axPost   next_axPost
                 (teqDiff tagAxPost   tagAxFan refl)
        hh  = hitAtTag  (natCode tagAxFan)    tagCode_axFan payT b body_axFan    next_axFan
                 (teqEq tagAxFan)
        be  = body_axFan_eval_param h1' h2' h' aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans hh be)))))))))

  -- For axZ x: body_axZ a b = Pair (Pair K_a1 payT) O
  --   where a = Pair tagCode_axKT payT, payT = Pair payZTagged payXT.
  --   This equals reify(outAxZ x) = reify(codeFormula (atomic (eqn (ap1 Z x) O))).
  body_axZ_eval : (x bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axZ
            (ap2 Pair tagCode_axKT (reify (nd (codeF1 Z) (code x)))) bb)
      (reify (outAxZ x))))
  body_axZ_eval x bb =
    let payZTagged = reify (codeF1 Z)
        payXT      = reify (code x)
        payT       = ap2 Pair payZTagged payXT
        a          = ap2 Pair tagCode_axKT payT
        K1V        = tagAp1
        K1         = reify K1V
        sndA       : Deriv (atomic (eqn (ap2 (Lift Snd) a bb) payT))
        sndA       = bodyLiftSndPair tagCode_axKT payT bb
        lhsBuild   = pairOfConst_eval K1V (Lift Snd) a bb payT sndA
        rhsKO      = liftKT_eval lf a bb           -- liftKT_eval Tree-indexed; lf gives O
    in pairOfFan_eval
         (Fan (Lift (KT K1)) (Lift Snd) Pair)
         (Lift (KT O)) a bb
         (ap2 Pair K1 payT) O
         lhsBuild rhsKO

  -- Parametric variant of body_axZ_eval: payload's xT-slot is a Term parameter
  -- rather than meta-computed reify (code x).  Used by Theorem 12's parametric
  -- dispatch in BRA/Thm12/Param/AxZ.agda.  Same proof structure as
  -- body_axZ_eval; payT directly takes any Term in the second component.
  body_axZ_eval_param : (xT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axZ
            (ap2 Pair tagCode_axKT (ap2 Pair (reify (codeF1 Z)) xT)) bb)
      (ap2 Pair (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 Z)) xT)) O)))
  body_axZ_eval_param xT bb =
    let payZTagged = reify (codeF1 Z)
        payT       = ap2 Pair payZTagged xT
        a          = ap2 Pair tagCode_axKT payT
        K1V        = tagAp1
        K1         = reify K1V
        sndA       : Deriv (atomic (eqn (ap2 (Lift Snd) a bb) payT))
        sndA       = bodyLiftSndPair tagCode_axKT payT bb
        lhsBuild   = pairOfConst_eval K1V (Lift Snd) a bb payT sndA
        rhsKO      = liftKT_eval lf a bb
    in pairOfFan_eval
         (Fan (Lift (KT K1)) (Lift Snd) Pair)
         (Lift (KT O)) a bb
         (ap2 Pair K1 payT) O
         lhsBuild rhsKO

  thmTDispAxZ : (x : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxZ x)))
                       (reify (outAxZ x))))
  thmTDispAxZ x =
    let payT = reify (nd (codeF1 Z) (code x))
        a   = ap2 Pair tagCode_axKT payT
        b   = ap2 Pair (ap1 thmT tagCode_axKT) (ap1 thmT payT)
        e1  = dispatchOpens tagAxFan payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axKT payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxKT refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axKT payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxKT refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axKT payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxKT refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axKT payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxKT refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axKT payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxKT refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axKT payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxKT refl)
        s7  = skipAtTag (natCode tagAxLift)   tagCode_axKT payT b body_axLift   next_axLift
                 (teqDiff tagAxLift   tagAxKT refl)
        s8  = skipAtTag (natCode tagAxPost)   tagCode_axKT payT b body_axPost   next_axPost
                 (teqDiff tagAxPost   tagAxKT refl)
        s9  = skipAtTag (natCode tagAxFan)    tagCode_axKT payT b body_axFan    next_axFan
                 (teqDiff tagAxFan    tagAxKT refl)
        hh  = hitAtTag  (natCode tagAxKT)    tagCode_axKT payT b body_axZ      next_axKT
                 (teqEq tagAxKT)
        be  = body_axZ_eval x b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans hh be))))))))))

  -- Parametric variant of thmTDispAxZ: payload's xT-slot is a Term
  -- parameter rather than meta-computed reify (code x).  Same cascade
  -- structure as thmTDispAxZ; body step uses body_axZ_eval_param.  Used
  -- by Theorem 12 (BRA/Thm12/Parts/Z.agda) where the asymmetric encoded
  -- equation puts  cor x  parametrically at the slot.
  thmTDispAxZ_param : (xT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axKT
                          (ap2 Pair (reify (codeF1 Z)) xT)))
      (ap2 Pair (ap2 Pair (reify tagAp1)
                          (ap2 Pair (reify (codeF1 Z)) xT)) O)))
  thmTDispAxZ_param xT =
    let payT = ap2 Pair (reify (codeF1 Z)) xT
        a   = ap2 Pair tagCode_axKT payT
        b   = ap2 Pair (ap1 thmT tagCode_axKT) (ap1 thmT payT)
        e1  = dispatchOpens tagAxFan payT
        s1  = skipAtTag (natCode tagAxI)      tagCode_axKT payT b body_axI      next_axI
                 (teqDiff tagAxI      tagAxKT refl)
        s2  = skipAtTag (natCode tagAxFst)    tagCode_axKT payT b body_axFst    next_axFst
                 (teqDiff tagAxFst    tagAxKT refl)
        s3  = skipAtTag (natCode tagAxSnd)    tagCode_axKT payT b body_axSnd    next_axSnd
                 (teqDiff tagAxSnd    tagAxKT refl)
        s4  = skipAtTag (natCode tagAxConst)  tagCode_axKT payT b body_axConst  next_axConst
                 (teqDiff tagAxConst  tagAxKT refl)
        s5  = skipAtTag (natCode tagAxComp)   tagCode_axKT payT b body_axComp   next_axComp
                 (teqDiff tagAxComp   tagAxKT refl)
        s6  = skipAtTag (natCode tagAxComp2)  tagCode_axKT payT b body_axComp2  next_axComp2
                 (teqDiff tagAxComp2  tagAxKT refl)
        s7  = skipAtTag (natCode tagAxLift)   tagCode_axKT payT b body_axLift   next_axLift
                 (teqDiff tagAxLift   tagAxKT refl)
        s8  = skipAtTag (natCode tagAxPost)   tagCode_axKT payT b body_axPost   next_axPost
                 (teqDiff tagAxPost   tagAxKT refl)
        s9  = skipAtTag (natCode tagAxFan)    tagCode_axKT payT b body_axFan    next_axFan
                 (teqDiff tagAxFan    tagAxKT refl)
        hh  = hitAtTag  (natCode tagAxKT)    tagCode_axKT payT b body_axZ      next_axKT
                 (teqEq tagAxKT)
        be  = body_axZ_eval_param xT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans hh be))))))))))

  ------------------------------------------------------------------
  -- Group II dispatch lemmas (Session D additions).
  --
  -- Same template as Group I:
  --   thmTDispX = dispatchOpens + (M-1) skipAtTag + hitAtTag + body_X_eval
  -- where M is X's tag position (axTreeEqLL = 17, axRecLf = 11, etc.).

  -- axTreeEqLL : 0 args; output = reify(outAxTreeEqLL), a closed constant.
  -- body = Lift (KT k); body_eval = liftKT_eval.
  body_axTreeEqLL_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqLL (ap2 Pair tagCode_axTreeEqLL O) b)
      (reify outAxTreeEqLL)))
  body_axTreeEqLL_eval b =
    liftKT_eval outAxTreeEqLL
                (ap2 Pair tagCode_axTreeEqLL O) b

  thmTDispAxTreeEqLL :
    Deriv (atomic (eqn (ap1 thmT (reify encAxTreeEqLL)) (reify outAxTreeEqLL)))
  thmTDispAxTreeEqLL =
    let payT = O
        a    = ap2 Pair tagCode_axTreeEqLL payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqLL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfN payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axTreeEqLL payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxTreeEqLL refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axTreeEqLL payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxTreeEqLL refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axTreeEqLL payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxTreeEqLL refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axTreeEqLL payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxTreeEqLL refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axTreeEqLL payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxTreeEqLL refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axTreeEqLL payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxTreeEqLL refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axTreeEqLL payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxTreeEqLL refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axTreeEqLL payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxTreeEqLL refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axTreeEqLL payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxTreeEqLL refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axTreeEqLL payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxTreeEqLL refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axTreeEqLL payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxTreeEqLL refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axTreeEqLL payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxTreeEqLL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axTreeEqLL payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxTreeEqLL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)  tagCode_axTreeEqLL payT b body_axRecPNd  next_axRecPNd
                  (teqDiff tagAxRecPNd  tagAxTreeEqLL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axTreeEqLL payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxTreeEqLL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)   tagCode_axTreeEqLL payT b body_axIfLfN   next_axIfLfN
                  (teqDiff tagAxIfLfN   tagAxTreeEqLL refl)
        hh   = hitAtTag  (natCode tagAxTreeEqLL) tagCode_axTreeEqLL payT b body_axTreeEqLL next_axTreeEqLL
                  (teqEq tagAxTreeEqLL)
        be   = body_axTreeEqLL_eval b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans hh be)))))))))))))))))

  -- axRecLf z s : 2 args (z : Term, s : Fun2); depth-2 payload.
  body_axRecLf_eval : (z : Term) (s : Fun2) (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecLf
            (ap2 Pair tagCode_axRecLf (reify (nd (code z) (codeF2 s)))) b)
      (reify (outAxRecLf z s))))
  body_axRecLf_eval z s b =
    let payZT  = reify (code z)
        payST  = reify (codeF2 s)
        payT   = ap2 Pair payZT payST
        a      = ap2 Pair tagCode_axRecLf payT
        K_a1V  = tagAp1
        K_a1   = reify K_a1V
        K_recV = leftT (codeF1 (Rec O IfLf))
        K_rec  = reify K_recV
        K_ooV  = lf                               -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        snd_a  = bodyLiftSndPair tagCode_axRecLf payT b
        ext_z  = liftCompFstSnd_evalPair tagCode_axRecLf payZT payST b
        kRecPayT = pairOfConst_eval K_recV (Lift Snd) a b payT snd_a
        kOO    = liftKT_eval K_ooV a b
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_rec)) (Lift Snd) Pair)
                   (Lift (KT K_oo))
                   a b
                   (ap2 Pair K_rec payT) K_oo
                   kRecPayT kOO
        lhsBuild = pairOfConst_eval K_a1V
                     (Fan (Fan (Lift (KT K_rec)) (Lift Snd) Pair)
                          (Lift (KT K_oo)) Pair)
                     a b
                     (ap2 Pair (ap2 Pair K_rec payT) K_oo)
                     midLHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_rec)) (Lift Snd) Pair)
                   (Lift (KT K_oo)) Pair)
              Pair)
         (Lift (Comp Fst Snd)) a b
         (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rec payT) K_oo)) payZT
         lhsBuild ext_z

  thmTDispAxRecLf : (z : Term) (s : Fun2) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxRecLf z s)))
                       (reify (outAxRecLf z s))))
  thmTDispAxRecLf z s =
    let payT = reify (nd (code z) (codeF2 s))
        a    = ap2 Pair tagCode_axRecLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecLf) (ap1 thmT payT)
        e1   = dispatchOpens tagAxKT payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecLf payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecLf refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecLf payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecLf refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecLf payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecLf refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecLf payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecLf refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecLf payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecLf refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecLf payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecLf refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecLf payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecLf refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecLf payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecLf refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecLf payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecLf refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecLf payT b body_axZ     next_axKT
                  (teqDiff tagAxKT     tagAxRecLf refl)
        hh   = hitAtTag  (natCode tagAxRecLf)  tagCode_axRecLf payT b body_axRecLf  next_axRecLf
                  (teqEq tagAxRecLf)
        be   = body_axRecLf_eval z s b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans hh be)))))))))))

  -- axIfLfL a b : 2 args; depth-2 payload.
  body_axIfLfL_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfL
            (ap2 Pair tagCode_axIfLfL (reify (nd (code a') (code b')))) bb)
      (reify (outAxIfLfL a' b'))))
  body_axIfLfL_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axIfLfL payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        snd_a  = bodyLiftSndPair tagCode_axIfLfL payT bb
        ext_a  = liftCompFstSnd_evalPair tagCode_axIfLfL payAT payBT bb
        l5 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        l3 = pairOfConst_eval K_ooV
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 a bb (ap2 Pair K_a2 (ap2 Pair K_pair payT)) l4
        l2 = pairOfConst_eval K_ifLfV
                 (Fan (Lift (KT K_oo))
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair) Pair)
                 a bb
                 (ap2 Pair K_oo (ap2 Pair K_a2 (ap2 Pair K_pair payT))) l3
        l1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_ifLf))
                      (Fan (Lift (KT K_oo))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_ifLf (ap2 Pair K_oo
                    (ap2 Pair K_a2 (ap2 Pair K_pair payT)))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Lift (KT K_oo))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf (ap2 Pair K_oo
            (ap2 Pair K_a2 (ap2 Pair K_pair payT))))) payAT
         l1 ext_a

  thmTDispAxIfLfL : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxIfLfL a' b')))
                       (reify (outAxIfLfL a' b'))))
  thmTDispAxIfLfL a' b' =
    let payT = reify (nd (code a') (code b'))
        a    = ap2 Pair tagCode_axIfLfL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecPNd payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axIfLfL payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxIfLfL refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axIfLfL payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxIfLfL refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axIfLfL payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxIfLfL refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axIfLfL payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxIfLfL refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axIfLfL payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxIfLfL refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axIfLfL payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxIfLfL refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axIfLfL payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxIfLfL refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axIfLfL payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxIfLfL refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axIfLfL payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxIfLfL refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axIfLfL payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxIfLfL refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axIfLfL payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxIfLfL refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axIfLfL payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxIfLfL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axIfLfL payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxIfLfL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)  tagCode_axIfLfL payT b body_axRecPNd  next_axRecPNd
                  (teqDiff tagAxRecPNd  tagAxIfLfL refl)
        hh   = hitAtTag  (natCode tagAxIfLfL)   tagCode_axIfLfL payT b body_axIfLfL   next_axIfLfL
                  (teqEq tagAxIfLfL)
        be   = body_axIfLfL_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans hh be)))))))))))))))

  -- Parametric variant of body_axIfLfL_eval (Theorem 12 / Parts/IfLf.agda).
  body_axIfLfL_eval_param : (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfL (ap2 Pair tagCode_axIfLfL (ap2 Pair aT bT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair O
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT))))))
        aT)))
  body_axIfLfL_eval_param aT bT bb =
    let payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axIfLfL payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_ooV  = lf
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        snd_a  = bodyLiftSndPair tagCode_axIfLfL payT bb
        ext_a  = liftCompFstSnd_evalPair tagCode_axIfLfL payAT payBT bb
        l5 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        l3 = pairOfConst_eval K_ooV
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 a bb (ap2 Pair K_a2 (ap2 Pair K_pair payT)) l4
        l2 = pairOfConst_eval K_ifLfV
                 (Fan (Lift (KT K_oo))
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair) Pair)
                 a bb
                 (ap2 Pair K_oo (ap2 Pair K_a2 (ap2 Pair K_pair payT))) l3
        l1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_ifLf))
                      (Fan (Lift (KT K_oo))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_ifLf (ap2 Pair K_oo
                    (ap2 Pair K_a2 (ap2 Pair K_pair payT)))) l2
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Lift (KT K_oo))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf (ap2 Pair K_oo
            (ap2 Pair K_a2 (ap2 Pair K_pair payT))))) payAT
         l1 ext_a

  -- Parametric variant of thmTDispAxIfLfL.
  thmTDispAxIfLfL_param : (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axIfLfL (ap2 Pair aT bT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair O
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT))))))
        aT)))
  thmTDispAxIfLfL_param aT bT =
    let payT = ap2 Pair aT bT
        a    = ap2 Pair tagCode_axIfLfL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecPNd payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axIfLfL payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxIfLfL refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axIfLfL payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxIfLfL refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axIfLfL payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxIfLfL refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axIfLfL payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxIfLfL refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axIfLfL payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxIfLfL refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axIfLfL payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxIfLfL refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axIfLfL payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxIfLfL refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axIfLfL payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxIfLfL refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axIfLfL payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxIfLfL refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axIfLfL payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxIfLfL refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axIfLfL payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxIfLfL refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axIfLfL payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxIfLfL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axIfLfL payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxIfLfL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)  tagCode_axIfLfL payT b body_axRecPNd  next_axRecPNd
                  (teqDiff tagAxRecPNd  tagAxIfLfL refl)
        hh   = hitAtTag  (natCode tagAxIfLfL)   tagCode_axIfLfL payT b body_axIfLfL   next_axIfLfL
                  (teqEq tagAxIfLfL)
        be   = body_axIfLfL_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans hh be)))))))))))))))

  -- axTreeEqLN a b : 2 args; depth-2 payload.
  body_axTreeEqLN_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqLN
            (ap2 Pair tagCode_axTreeEqLN (reify (nd (code a') (code b')))) bb)
      (reify (outAxTreeEqLN a' b'))))
  body_axTreeEqLN_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axTreeEqLN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rhsV = code (ap2 Pair O O)
        K_rhs  = reify K_rhsV
        snd_a  = bodyLiftSndPair tagCode_axTreeEqLN payT bb
        l5 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        l3 = pairOfConst_eval K_ooV
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 a bb (ap2 Pair K_a2 (ap2 Pair K_pair payT)) l4
        l2 = pairOfConst_eval K_teV
                 (Fan (Lift (KT K_oo))
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair) Pair)
                 a bb
                 (ap2 Pair K_oo (ap2 Pair K_a2 (ap2 Pair K_pair payT))) l3
        l1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_te))
                      (Fan (Lift (KT K_oo))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_te (ap2 Pair K_oo
                    (ap2 Pair K_a2 (ap2 Pair K_pair payT)))) l2
        rhs = liftKT_eval K_rhsV a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Lift (KT K_oo))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair K_oo
            (ap2 Pair K_a2 (ap2 Pair K_pair payT))))) K_rhs
         l1 rhs

  thmTDispAxTreeEqLN : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxTreeEqLN a' b')))
                       (reify (outAxTreeEqLN a' b'))))
  thmTDispAxTreeEqLN a' b' =
    let payT = reify (nd (code a') (code b'))
        a    = ap2 Pair tagCode_axTreeEqLN payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqLN) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqLL payT
        s1   = skipAtTag (natCode tagAxI)        tagCode_axTreeEqLN payT b body_axI        next_axI
                  (teqDiff tagAxI        tagAxTreeEqLN refl)
        s2   = skipAtTag (natCode tagAxFst)      tagCode_axTreeEqLN payT b body_axFst      next_axFst
                  (teqDiff tagAxFst      tagAxTreeEqLN refl)
        s3   = skipAtTag (natCode tagAxSnd)      tagCode_axTreeEqLN payT b body_axSnd      next_axSnd
                  (teqDiff tagAxSnd      tagAxTreeEqLN refl)
        s4   = skipAtTag (natCode tagAxConst)    tagCode_axTreeEqLN payT b body_axConst    next_axConst
                  (teqDiff tagAxConst    tagAxTreeEqLN refl)
        s5   = skipAtTag (natCode tagAxComp)     tagCode_axTreeEqLN payT b body_axComp     next_axComp
                  (teqDiff tagAxComp     tagAxTreeEqLN refl)
        s6   = skipAtTag (natCode tagAxComp2)    tagCode_axTreeEqLN payT b body_axComp2    next_axComp2
                  (teqDiff tagAxComp2    tagAxTreeEqLN refl)
        s7   = skipAtTag (natCode tagAxLift)     tagCode_axTreeEqLN payT b body_axLift     next_axLift
                  (teqDiff tagAxLift     tagAxTreeEqLN refl)
        s8   = skipAtTag (natCode tagAxPost)     tagCode_axTreeEqLN payT b body_axPost     next_axPost
                  (teqDiff tagAxPost     tagAxTreeEqLN refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axTreeEqLN payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxTreeEqLN refl)
        s10  = skipAtTag (natCode tagAxKT)       tagCode_axTreeEqLN payT b body_axZ       next_axKT
                  (teqDiff tagAxKT       tagAxTreeEqLN refl)
        s11  = skipAtTag (natCode tagAxRecLf)    tagCode_axTreeEqLN payT b body_axRecLf    next_axRecLf
                  (teqDiff tagAxRecLf    tagAxTreeEqLN refl)
        s12  = skipAtTag (natCode tagAxRecNd)    tagCode_axTreeEqLN payT b body_axRecNd    next_axRecNd
                  (teqDiff tagAxRecNd    tagAxTreeEqLN refl)
        s13  = skipAtTag (natCode tagAxRecPLf)   tagCode_axTreeEqLN payT b body_axRecPLf   next_axRecPLf
                  (teqDiff tagAxRecPLf   tagAxTreeEqLN refl)
        s14  = skipAtTag (natCode tagAxRecPNd)   tagCode_axTreeEqLN payT b body_axRecPNd   next_axRecPNd
                  (teqDiff tagAxRecPNd   tagAxTreeEqLN refl)
        s15  = skipAtTag (natCode tagAxIfLfL)    tagCode_axTreeEqLN payT b body_axIfLfL    next_axIfLfL
                  (teqDiff tagAxIfLfL    tagAxTreeEqLN refl)
        s16  = skipAtTag (natCode tagAxIfLfN)    tagCode_axTreeEqLN payT b body_axIfLfN    next_axIfLfN
                  (teqDiff tagAxIfLfN    tagAxTreeEqLN refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL) tagCode_axTreeEqLN payT b body_axTreeEqLL next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL tagAxTreeEqLN refl)
        hh   = hitAtTag  (natCode tagAxTreeEqLN) tagCode_axTreeEqLN payT b body_axTreeEqLN next_axTreeEqLN
                  (teqEq tagAxTreeEqLN)
        be   = body_axTreeEqLN_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans hh be))))))))))))))))))

  -- axTreeEqNL a b : 2 args; depth-2 payload.  Mirror of axTreeEqLN.
  body_axTreeEqNL_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqNL
            (ap2 Pair tagCode_axTreeEqNL (reify (nd (code a') (code b')))) bb)
      (reify (outAxTreeEqNL a' b'))))
  body_axTreeEqNL_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axTreeEqNL payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rhsV = code (ap2 Pair O O)
        K_rhs  = reify K_rhsV
        snd_a  = bodyLiftSndPair tagCode_axTreeEqNL payT bb
        l5 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        kOO = liftKT_eval K_ooV a bb
        l3 = pairOfFan_eval
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 (Lift (KT K_oo)) a bb
                 (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo
                 l4 kOO
        l2 = pairOfConst_eval K_teV
                 (Fan (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                      (Lift (KT K_oo)) Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo) l3
        l1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_te))
                      (Fan (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           (Lift (KT K_oo)) Pair) Pair)
                 a bb
                 (ap2 Pair K_te
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo)) l2
        rhs = liftKT_eval K_rhsV a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        (Lift (KT K_oo)) Pair) Pair) Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_te
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo))) K_rhs
         l1 rhs

  thmTDispAxTreeEqNL : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxTreeEqNL a' b')))
                       (reify (outAxTreeEqNL a' b'))))
  thmTDispAxTreeEqNL a' b' =
    let payT = reify (nd (code a') (code b'))
        a    = ap2 Pair tagCode_axTreeEqNL payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqNL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqLN payT
        s1   = skipAtTag (natCode tagAxI)        tagCode_axTreeEqNL payT b body_axI        next_axI
                  (teqDiff tagAxI        tagAxTreeEqNL refl)
        s2   = skipAtTag (natCode tagAxFst)      tagCode_axTreeEqNL payT b body_axFst      next_axFst
                  (teqDiff tagAxFst      tagAxTreeEqNL refl)
        s3   = skipAtTag (natCode tagAxSnd)      tagCode_axTreeEqNL payT b body_axSnd      next_axSnd
                  (teqDiff tagAxSnd      tagAxTreeEqNL refl)
        s4   = skipAtTag (natCode tagAxConst)    tagCode_axTreeEqNL payT b body_axConst    next_axConst
                  (teqDiff tagAxConst    tagAxTreeEqNL refl)
        s5   = skipAtTag (natCode tagAxComp)     tagCode_axTreeEqNL payT b body_axComp     next_axComp
                  (teqDiff tagAxComp     tagAxTreeEqNL refl)
        s6   = skipAtTag (natCode tagAxComp2)    tagCode_axTreeEqNL payT b body_axComp2    next_axComp2
                  (teqDiff tagAxComp2    tagAxTreeEqNL refl)
        s7   = skipAtTag (natCode tagAxLift)     tagCode_axTreeEqNL payT b body_axLift     next_axLift
                  (teqDiff tagAxLift     tagAxTreeEqNL refl)
        s8   = skipAtTag (natCode tagAxPost)     tagCode_axTreeEqNL payT b body_axPost     next_axPost
                  (teqDiff tagAxPost     tagAxTreeEqNL refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axTreeEqNL payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxTreeEqNL refl)
        s10  = skipAtTag (natCode tagAxKT)       tagCode_axTreeEqNL payT b body_axZ       next_axKT
                  (teqDiff tagAxKT       tagAxTreeEqNL refl)
        s11  = skipAtTag (natCode tagAxRecLf)    tagCode_axTreeEqNL payT b body_axRecLf    next_axRecLf
                  (teqDiff tagAxRecLf    tagAxTreeEqNL refl)
        s12  = skipAtTag (natCode tagAxRecNd)    tagCode_axTreeEqNL payT b body_axRecNd    next_axRecNd
                  (teqDiff tagAxRecNd    tagAxTreeEqNL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)   tagCode_axTreeEqNL payT b body_axRecPLf   next_axRecPLf
                  (teqDiff tagAxRecPLf   tagAxTreeEqNL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)   tagCode_axTreeEqNL payT b body_axRecPNd   next_axRecPNd
                  (teqDiff tagAxRecPNd   tagAxTreeEqNL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)    tagCode_axTreeEqNL payT b body_axIfLfL    next_axIfLfL
                  (teqDiff tagAxIfLfL    tagAxTreeEqNL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)    tagCode_axTreeEqNL payT b body_axIfLfN    next_axIfLfN
                  (teqDiff tagAxIfLfN    tagAxTreeEqNL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL) tagCode_axTreeEqNL payT b body_axTreeEqLL next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL tagAxTreeEqNL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN) tagCode_axTreeEqNL payT b body_axTreeEqLN next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN tagAxTreeEqNL refl)
        hh   = hitAtTag  (natCode tagAxTreeEqNL) tagCode_axTreeEqNL payT b body_axTreeEqNL next_axTreeEqNL
                  (teqEq tagAxTreeEqNL)
        be   = body_axTreeEqNL_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans hh be)))))))))))))))))))

  -- axGoodstein a b : 2 args; depth-2 payload.  LHS and RHS are big.
  body_axGoodstein_eval : (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axGoodstein
            (ap2 Pair tagCode_axGoodstein (reify (nd (code a') (code b')))) bb)
      (reify (outAxGoodstein a' b'))))
  body_axGoodstein_eval a' b' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axGoodstein payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        snd_a  = bodyLiftSndPair tagCode_axGoodstein payT bb
        ext_a  = liftCompFstSnd_evalPair tagCode_axGoodstein payAT payBT bb
        ext_b  = liftCompSndSnd_evalPair tagCode_axGoodstein payAT payBT bb
        kOO    = liftKT_eval K_ooV a bb
        -- Shared TreeEq-part: (Pair K_a2 (Pair K_te payT))
        teInner = pairOfConst_eval K_teV (Lift Snd) a bb payT snd_a
        teFull  = pairOfConst_eval K_a2V
                    (Fan (Lift (KT K_te)) (Lift Snd) Pair) a bb
                    (ap2 Pair K_te payT) teInner
        -- LHS Pair-part: (Pair K_a2 (Pair K_pair (Pair payAT K_oo)))
        l_aoo  = pairOfFan_eval (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                    a bb payAT K_oo ext_a kOO
        l_pair = pairOfConst_eval K_pairV
                    (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo)) Pair)
                    a bb (ap2 Pair payAT K_oo) l_aoo
        l_pFull = pairOfConst_eval K_a2V
                    (Fan (Lift (KT K_pair))
                         (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo)) Pair)
                         Pair)
                    a bb (ap2 Pair K_pair (ap2 Pair payAT K_oo)) l_pair
        -- LHS inner Fan: Pair (te-part) (pair-part)
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_te payT))
                      (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payAT K_oo)))
                      teFull l_pFull
        lhs_ifLf = pairOfConst_eval K_ifLfV
                     (Fan (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair))
                                    (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                (ap2 Pair K_a2
                                  (ap2 Pair K_pair (ap2 Pair payAT K_oo))))
                     lhs_inner
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te)) (Lift Snd) Pair)
                                    Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (KT K_oo))
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair (ap2 Pair payAT K_oo)))))
                     lhs_ifLf
        -- RHS Pair-part: (Pair K_a2 (Pair K_pair (Pair payBT K_oo)))
        r_boo  = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                    a bb payBT K_oo ext_b kOO
        r_pair = pairOfConst_eval K_pairV
                    (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                    a bb (ap2 Pair payBT K_oo) r_boo
        r_pFull = pairOfConst_eval K_a2V
                    (Fan (Lift (KT K_pair))
                         (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                         Pair)
                    a bb (ap2 Pair K_pair (ap2 Pair payBT K_oo)) r_pair
        rhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_te payT))
                      (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payBT K_oo)))
                      teFull r_pFull
        rhs_ifLf = pairOfConst_eval K_ifLfV
                     (Fan (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair))
                                    (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                (ap2 Pair K_a2
                                  (ap2 Pair K_pair (ap2 Pair payBT K_oo))))
                     rhs_inner
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te)) (Lift Snd) Pair)
                                    Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Snd Snd))
                                              (Lift (KT K_oo))
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair (ap2 Pair payBT K_oo)))))
                     rhs_ifLf
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd)) (Lift (KT K_oo))
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te)) (Lift Snd) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                       (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payAT K_oo))))))
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te payT))
                       (ap2 Pair K_a2
                         (ap2 Pair K_pair (ap2 Pair payBT K_oo))))))
         lhsBuild rhsBuild

  thmTDispAxGoodstein : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxGoodstein a' b')))
                       (reify (outAxGoodstein a' b'))))
  thmTDispAxGoodstein a' b' =
    let payT = reify (nd (code a') (code b'))
        a    = ap2 Pair tagCode_axGoodstein payT
        b    = ap2 Pair (ap1 thmT tagCode_axGoodstein) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqNN payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axGoodstein payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxGoodstein refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axGoodstein payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxGoodstein refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axGoodstein payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxGoodstein refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axGoodstein payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxGoodstein refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axGoodstein payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxGoodstein refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axGoodstein payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxGoodstein refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axGoodstein payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxGoodstein refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axGoodstein payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxGoodstein refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axGoodstein payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxGoodstein refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axGoodstein payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxGoodstein refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axGoodstein payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxGoodstein refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axGoodstein payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxGoodstein refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axGoodstein payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxGoodstein refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axGoodstein payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxGoodstein refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axGoodstein payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxGoodstein refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axGoodstein payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxGoodstein refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axGoodstein payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxGoodstein refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axGoodstein payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxGoodstein refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axGoodstein payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxGoodstein refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axGoodstein payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxGoodstein refl)
        hh   = hitAtTag  (natCode tagAxGoodstein) tagCode_axGoodstein payT b body_axGoodstein next_axGoodstein
                  (teqEq tagAxGoodstein)
        be   = body_axGoodstein_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans hh be)))))))))))))))))))))

  -- axIfLfN x y a b : 4 args; depth-4 payload.
  body_axIfLfN_eval : (x y a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfN
            (ap2 Pair tagCode_axIfLfN
              (reify (nd (code x) (nd (code y) (nd (code a') (code b')))))) bb)
      (reify (outAxIfLfN x y a' b'))))
  body_axIfLfN_eval x y a' b' bb =
    let payX   = reify (code x)
        payY   = reify (code y)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payX (ap2 Pair payY (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axIfLfN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        ext_x  = liftCompFstSnd_evalPair tagCode_axIfLfN payX
                   (ap2 Pair payY (ap2 Pair payAT payBT)) bb
        ext_y  = liftFstSndSnd_evalPair3 tagCode_axIfLfN payX payY
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axIfLfN payX payY payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axIfLfN payX payY payAT payBT bb
        -- xy-block: (Pair K_a2 (Pair K_pair (Pair payX payY)))
        xy_pair  = pairOfFan_eval (Lift (Comp Fst Snd))
                     (Lift (Comp Fst (Comp Snd Snd))) a bb
                     payX payY ext_x ext_y
        xy_KP    = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payX payY) xy_pair
        xy_full  = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payX payY)) xy_KP
        -- ab-block: (Pair K_a2 (Pair K_pair (Pair payAT payBT)))
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        ab_KP    = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        ab_full  = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) ab_KP
        -- Combine xy and ab.
        xy_ab    = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair))
                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payX payY)))
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                     xy_full ab_full
        ifLf_inner = pairOfConst_eval K_ifLfV
                       (Fan (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst Snd))
                                           (Lift (Comp Fst (Comp Snd Snd)))
                                           Pair)
                                      Pair) Pair)
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payX payY)))
                                  (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       xy_ab
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd Snd)))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payX payY)))
                                  (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     ifLf_inner
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payX payY)))
                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         payBT
         lhsBuild ext_b

  thmTDispAxIfLfN : (x y a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxIfLfN x y a' b')))
                       (reify (outAxIfLfN x y a' b'))))
  thmTDispAxIfLfN x y a' b' =
    let payT = reify (nd (code x) (nd (code y) (nd (code a') (code b'))))
        a    = ap2 Pair tagCode_axIfLfN payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfN) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfL payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axIfLfN payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxIfLfN refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axIfLfN payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxIfLfN refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axIfLfN payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxIfLfN refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axIfLfN payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxIfLfN refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axIfLfN payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxIfLfN refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axIfLfN payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxIfLfN refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axIfLfN payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxIfLfN refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axIfLfN payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxIfLfN refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axIfLfN payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxIfLfN refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axIfLfN payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxIfLfN refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axIfLfN payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxIfLfN refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axIfLfN payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxIfLfN refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axIfLfN payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxIfLfN refl)
        s14  = skipAtTag (natCode tagAxRecPNd)  tagCode_axIfLfN payT b body_axRecPNd  next_axRecPNd
                  (teqDiff tagAxRecPNd  tagAxIfLfN refl)
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axIfLfN payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxIfLfN refl)
        hh   = hitAtTag  (natCode tagAxIfLfN)   tagCode_axIfLfN payT b body_axIfLfN   next_axIfLfN
                  (teqEq tagAxIfLfN)
        be   = body_axIfLfN_eval x y a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans hh be))))))))))))))))

  -- Parametric variant of body_axIfLfN_eval (Theorem 12 / Parts/IfLf.agda).
  body_axIfLfN_eval_param : (xT yT aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfN
        (ap2 Pair tagCode_axIfLfN
          (ap2 Pair xT (ap2 Pair yT (ap2 Pair aT bT)))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair xT yT)))
                      (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair aT bT))))))
        bT)))
  body_axIfLfN_eval_param xT yT aT bT bb =
    let payX   = xT
        payY   = yT
        payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payX (ap2 Pair payY (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axIfLfN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        ext_x  = liftCompFstSnd_evalPair tagCode_axIfLfN payX
                   (ap2 Pair payY (ap2 Pair payAT payBT)) bb
        ext_y  = liftFstSndSnd_evalPair3 tagCode_axIfLfN payX payY
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axIfLfN payX payY payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axIfLfN payX payY payAT payBT bb
        xy_pair  = pairOfFan_eval (Lift (Comp Fst Snd))
                     (Lift (Comp Fst (Comp Snd Snd))) a bb
                     payX payY ext_x ext_y
        xy_KP    = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payX payY) xy_pair
        xy_full  = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payX payY)) xy_KP
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        ab_KP    = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        ab_full  = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) ab_KP
        xy_ab    = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair))
                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payX payY)))
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                     xy_full ab_full
        ifLf_inner = pairOfConst_eval K_ifLfV
                       (Fan (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst Snd))
                                           (Lift (Comp Fst (Comp Snd Snd)))
                                           Pair)
                                      Pair) Pair)
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payX payY)))
                                  (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       xy_ab
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd Snd)))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payX payY)))
                                  (ap2 Pair K_a2
                                   (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     ifLf_inner
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
         (ap2 Pair K_a2 (ap2 Pair K_ifLf
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payX payY)))
                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         payBT
         lhsBuild ext_b

  -- Parametric variant of thmTDispAxIfLfN.
  thmTDispAxIfLfN_param : (xT yT aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axIfLfN
        (ap2 Pair xT (ap2 Pair yT (ap2 Pair aT bT)))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair xT yT)))
                      (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair aT bT))))))
        bT)))
  thmTDispAxIfLfN_param xT yT aT bT =
    let payT = ap2 Pair xT (ap2 Pair yT (ap2 Pair aT bT))
        a    = ap2 Pair tagCode_axIfLfN payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfN) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfL payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axIfLfN payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxIfLfN refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axIfLfN payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxIfLfN refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axIfLfN payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxIfLfN refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axIfLfN payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxIfLfN refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axIfLfN payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxIfLfN refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axIfLfN payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxIfLfN refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axIfLfN payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxIfLfN refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axIfLfN payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxIfLfN refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axIfLfN payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxIfLfN refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axIfLfN payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxIfLfN refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axIfLfN payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxIfLfN refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axIfLfN payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxIfLfN refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axIfLfN payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxIfLfN refl)
        s14  = skipAtTag (natCode tagAxRecPNd)  tagCode_axIfLfN payT b body_axRecPNd  next_axRecPNd
                  (teqDiff tagAxRecPNd  tagAxIfLfN refl)
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axIfLfN payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxIfLfN refl)
        hh   = hitAtTag  (natCode tagAxIfLfN)   tagCode_axIfLfN payT b body_axIfLfN   next_axIfLfN
                  (teqEq tagAxIfLfN)
        be   = body_axIfLfN_eval_param xT yT aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans hh be))))))))))))))))

  -- axRecPLf s p : 2 args (s : Fun2, p : Term); depth-2 payload.
  body_axRecPLf_eval : (s : Fun2) (p : Term) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecPLf
            (ap2 Pair tagCode_axRecPLf (reify (nd (codeF2 s) (code p)))) bb)
      (reify (outAxRecPLf s p))))
  body_axRecPLf_eval s p bb =
    let payST  = reify (codeF2 s)
        payPT  = reify (code p)
        payT   = ap2 Pair payST payPT
        a      = ap2 Pair tagCode_axRecPLf payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_rPV  = leftT (codeF2 (RecP IfLf))
        K_rP   = reify K_rPV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        K_rhsV = lf                                -- post-redesign: reify (code O) = O
        K_rhs  = reify K_rhsV
        ext_s  = liftCompFstSnd_evalPair tagCode_axRecPLf payST payPT bb
        ext_p  = liftCompSndSnd_evalPair tagCode_axRecPLf payST payPT bb
        kOO    = liftKT_eval K_ooV a bb
        l_recPS = pairOfConst_eval K_rPV (Lift (Comp Fst Snd)) a bb payST ext_s
        l_pOO   = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                    a bb payPT K_oo ext_p kOO
        l_inner = pairOfFan_eval
                    (Fan (Lift (KT K_rP)) (Lift (Comp Fst Snd)) Pair)
                    (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                    a bb
                    (ap2 Pair K_rP payST)
                    (ap2 Pair payPT K_oo)
                    l_recPS l_pOO
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_rP)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rP payST) (ap2 Pair payPT K_oo))
                     l_inner
        rhs = liftKT_eval K_rhsV a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_rP)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair) Pair)
              Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rP payST)
                                    (ap2 Pair payPT K_oo)))
         K_rhs
         lhsBuild rhs

  thmTDispAxRecPLf : (s : Fun2) (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxRecPLf s p)))
                       (reify (outAxRecPLf s p))))
  thmTDispAxRecPLf s p =
    let payT = reify (nd (codeF2 s) (code p))
        a    = ap2 Pair tagCode_axRecPLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecPLf) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecNd payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecPLf payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecPLf refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecPLf payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecPLf refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecPLf payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecPLf refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecPLf payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecPLf refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecPLf payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecPLf refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecPLf payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecPLf refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecPLf payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecPLf refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecPLf payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecPLf refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecPLf payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecPLf refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecPLf payT b body_axZ     next_axKT
                  (teqDiff tagAxKT     tagAxRecPLf refl)
        s11  = skipAtTag (natCode tagAxRecLf)  tagCode_axRecPLf payT b body_axRecLf  next_axRecLf
                  (teqDiff tagAxRecLf  tagAxRecPLf refl)
        s12  = skipAtTag (natCode tagAxRecNd)  tagCode_axRecPLf payT b body_axRecNd  next_axRecNd
                  (teqDiff tagAxRecNd  tagAxRecPLf refl)
        hh   = hitAtTag  (natCode tagAxRecPLf) tagCode_axRecPLf payT b body_axRecPLf next_axRecPLf
                  (teqEq tagAxRecPLf)
        be   = body_axRecPLf_eval s p b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans hh be)))))))))))))

  -- axTreeEqNN a1 a2 b1 b2 : 4 args; depth-4 payload.  Two large branches.
  body_axTreeEqNN_eval : (a1 a2 b1 b2 bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqNN
            (ap2 Pair tagCode_axTreeEqNN
              (reify (nd (code a1) (nd (code a2) (nd (code b1) (code b2)))))) bb)
      (reify (outAxTreeEqNN a1 a2 b1 b2))))
  body_axTreeEqNN_eval a1 a2 b1 b2 bb =
    let payA1  = reify (code a1)
        payA2  = reify (code a2)
        payB1  = reify (code b1)
        payB2  = reify (code b2)
        payT   = ap2 Pair payA1 (ap2 Pair payA2 (ap2 Pair payB1 payB2))
        a      = ap2 Pair tagCode_axTreeEqNN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_ooV  = lf                                -- post-redesign: code O = lf, reify = O
        K_oo   = reify K_ooV
        ext_a1 = liftCompFstSnd_evalPair tagCode_axTreeEqNN payA1
                   (ap2 Pair payA2 (ap2 Pair payB1 payB2)) bb
        ext_a2 = liftFstSndSnd_evalPair3 tagCode_axTreeEqNN payA1 payA2
                   (ap2 Pair payB1 payB2) bb
        ext_b1 = liftFstSndSndSnd_evalPair4 tagCode_axTreeEqNN payA1 payA2 payB1 payB2 bb
        ext_b2 = liftSndSndSndSnd_evalPair4 tagCode_axTreeEqNN payA1 payA2 payB1 payB2 bb
        kOO    = liftKT_eval K_ooV a bb
        ----------------------------------------------------------------
        -- LHS shape: Pair K_a2 (Pair K_te
        --              (Pair (Pair K_a2 (Pair K_pair (Pair payA1 payA2)))
        --                    (Pair K_a2 (Pair K_pair (Pair payB1 payB2)))))
        a1a2   = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) a bb
                   payA1 payA2 ext_a1 ext_a2
        ka1a2  = pairOfConst_eval K_pairV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payA1 payA2) a1a2
        a_full = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair payA1 payA2)) ka1a2
        b1b2   = pairOfFan_eval (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                   payB1 payB2 ext_b1 ext_b2
        kb1b2  = pairOfConst_eval K_pairV
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payB1 payB2) b1b2
        b_full = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair payB1 payB2)) kb1b2
        l_inner = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
                              Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                   Pair)
                              Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2)))
                    a_full b_full
        l_te   = pairOfConst_eval K_teV
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                              (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2))))
                   l_inner
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_te))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd Snd)))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_te
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2)))))
                     l_te
        ----------------------------------------------------------------
        -- RHS shape: Pair K_a2 (Pair K_ifLf
        --              (Pair (Pair K_a2 (Pair K_te (Pair payA1 payB1)))
        --                    (Pair K_a2 (Pair K_pair
        --                      (Pair (Pair K_a2 (Pair K_te (Pair payA2 payB2)))
        --                            (Pair K_a2 (Pair K_pair (Pair K_oo K_oo))))))))
        -- Block A: (Pair K_a2 (Pair K_te (Pair payA1 payB1)))
        a1b1   = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                   payA1 payB1 ext_a1 ext_b1
        kA1B1  = pairOfConst_eval K_teV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payA1 payB1) a1b1
        blkA   = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_te))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_te (ap2 Pair payA1 payB1)) kA1B1
        -- Block B-inner: (Pair K_a2 (Pair K_te (Pair payA2 payB2)))
        a2b2   = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                   payA2 payB2 ext_a2 ext_b2
        kA2B2  = pairOfConst_eval K_teV
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payA2 payB2) a2b2
        blkBin = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_te))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_te (ap2 Pair payA2 payB2)) kA2B2
        -- Block PairOO-coded: (Pair K_a2 (Pair K_pair (Pair K_oo K_oo)))
        ooOO   = pairOfFan_eval (Lift (KT K_oo)) (Lift (KT K_oo))
                   a bb K_oo K_oo kOO kOO
        kPOO   = pairOfConst_eval K_pairV
                   (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                   a bb (ap2 Pair K_oo K_oo) ooOO
        blkPOO = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair) Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair K_oo K_oo)) kPOO
        -- Block C: (Pair K_a2 (Pair K_pair (Pair blkBin blkPOO)))
        binPOO = pairOfFan_eval
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_te))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_pair))
                             (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                   (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))
                   blkBin blkPOO
        kBinPOO = pairOfConst_eval K_pairV
                    (Fan (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_te))
                                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                        Pair)
                                   Pair) Pair)
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                                   Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))
                    binPOO
        blkC   = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_te))
                                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                            Pair)
                                       Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                                       Pair) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_pair
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))
                   kBinPOO
        -- Combine blkA and blkC -> inner Pair
        r_inner = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_te))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                              Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Fan (Lift (KT K_a2))
                                        (Fan (Lift (KT K_te))
                                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                  Pair)
                                             Pair) Pair)
                                   (Fan (Lift (KT K_a2))
                                        (Fan (Lift (KT K_pair))
                                             (Fan (Lift (KT K_oo)) (Lift (KT K_oo))
                                                  Pair)
                                             Pair) Pair)
                                   Pair) Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                    (ap2 Pair K_a2
                      (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))))
                    blkA blkC
        r_ifLf  = pairOfConst_eval K_ifLfV
                    (Fan (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_te))
                                   (Fan (Lift (Comp Fst Snd))
                                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                                   Pair) Pair)
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Fan (Lift (KT K_a2))
                                             (Fan (Lift (KT K_te))
                                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                       Pair)
                                                  Pair) Pair)
                                        (Fan (Lift (KT K_a2))
                                             (Fan (Lift (KT K_pair))
                                                  (Fan (Lift (KT K_oo)) (Lift (KT K_oo))
                                                       Pair)
                                                  Pair) Pair)
                                        Pair) Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                               (ap2 Pair K_a2
                                 (ap2 Pair K_pair
                                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                              (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))))
                    r_inner
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_te))
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_pair))
                                                        (Fan (Lift (KT K_oo))
                                                             (Lift (KT K_oo))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair
                                      (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                                 (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))))))
                     r_ifLf
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_te))
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_pair))
                                                 (Fan (Lift (KT K_oo))
                                                      (Lift (KT K_oo))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair K_te
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2))))))
         (ap2 Pair K_a2
           (ap2 Pair K_ifLf
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                        (ap2 Pair K_a2
                          (ap2 Pair K_pair
                            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))))))
         lhsBuild rhsBuild

  thmTDispAxTreeEqNN : (a1 a2 b1 b2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxTreeEqNN a1 a2 b1 b2)))
                       (reify (outAxTreeEqNN a1 a2 b1 b2))))
  thmTDispAxTreeEqNN a1 a2 b1 b2 =
    let payT = reify (nd (code a1) (nd (code a2) (nd (code b1) (code b2))))
        a    = ap2 Pair tagCode_axTreeEqNN payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqNN) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqNL payT
        s1   = skipAtTag (natCode tagAxI)        tagCode_axTreeEqNN payT b body_axI        next_axI
                  (teqDiff tagAxI        tagAxTreeEqNN refl)
        s2   = skipAtTag (natCode tagAxFst)      tagCode_axTreeEqNN payT b body_axFst      next_axFst
                  (teqDiff tagAxFst      tagAxTreeEqNN refl)
        s3   = skipAtTag (natCode tagAxSnd)      tagCode_axTreeEqNN payT b body_axSnd      next_axSnd
                  (teqDiff tagAxSnd      tagAxTreeEqNN refl)
        s4   = skipAtTag (natCode tagAxConst)    tagCode_axTreeEqNN payT b body_axConst    next_axConst
                  (teqDiff tagAxConst    tagAxTreeEqNN refl)
        s5   = skipAtTag (natCode tagAxComp)     tagCode_axTreeEqNN payT b body_axComp     next_axComp
                  (teqDiff tagAxComp     tagAxTreeEqNN refl)
        s6   = skipAtTag (natCode tagAxComp2)    tagCode_axTreeEqNN payT b body_axComp2    next_axComp2
                  (teqDiff tagAxComp2    tagAxTreeEqNN refl)
        s7   = skipAtTag (natCode tagAxLift)     tagCode_axTreeEqNN payT b body_axLift     next_axLift
                  (teqDiff tagAxLift     tagAxTreeEqNN refl)
        s8   = skipAtTag (natCode tagAxPost)     tagCode_axTreeEqNN payT b body_axPost     next_axPost
                  (teqDiff tagAxPost     tagAxTreeEqNN refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axTreeEqNN payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxTreeEqNN refl)
        s10  = skipAtTag (natCode tagAxKT)       tagCode_axTreeEqNN payT b body_axZ       next_axKT
                  (teqDiff tagAxKT       tagAxTreeEqNN refl)
        s11  = skipAtTag (natCode tagAxRecLf)    tagCode_axTreeEqNN payT b body_axRecLf    next_axRecLf
                  (teqDiff tagAxRecLf    tagAxTreeEqNN refl)
        s12  = skipAtTag (natCode tagAxRecNd)    tagCode_axTreeEqNN payT b body_axRecNd    next_axRecNd
                  (teqDiff tagAxRecNd    tagAxTreeEqNN refl)
        s13  = skipAtTag (natCode tagAxRecPLf)   tagCode_axTreeEqNN payT b body_axRecPLf   next_axRecPLf
                  (teqDiff tagAxRecPLf   tagAxTreeEqNN refl)
        s14  = skipAtTag (natCode tagAxRecPNd)   tagCode_axTreeEqNN payT b body_axRecPNd   next_axRecPNd
                  (teqDiff tagAxRecPNd   tagAxTreeEqNN refl)
        s15  = skipAtTag (natCode tagAxIfLfL)    tagCode_axTreeEqNN payT b body_axIfLfL    next_axIfLfL
                  (teqDiff tagAxIfLfL    tagAxTreeEqNN refl)
        s16  = skipAtTag (natCode tagAxIfLfN)    tagCode_axTreeEqNN payT b body_axIfLfN    next_axIfLfN
                  (teqDiff tagAxIfLfN    tagAxTreeEqNN refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL) tagCode_axTreeEqNN payT b body_axTreeEqLL next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL tagAxTreeEqNN refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN) tagCode_axTreeEqNN payT b body_axTreeEqLN next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN tagAxTreeEqNN refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL) tagCode_axTreeEqNN payT b body_axTreeEqNL next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL tagAxTreeEqNN refl)
        hh   = hitAtTag  (natCode tagAxTreeEqNN) tagCode_axTreeEqNN payT b body_axTreeEqNN next_axTreeEqNN
                  (teqEq tagAxTreeEqNN)
        be   = body_axTreeEqNN_eval a1 a2 b1 b2 b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans hh be))))))))))))))))))))

  -- axRecPNd s p a b : 4 args; depth-4 payload; large RHS with 2 recursive
  -- (RecP s p X) sub-codes.
  body_axRecPNd_eval : (s : Fun2) (p a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecPNd
            (ap2 Pair tagCode_axRecPNd
              (reify (nd (codeF2 s) (nd (code p) (nd (code a') (code b')))))) bb)
      (reify (outAxRecPNd s p a' b'))))
  body_axRecPNd_eval s p a' b' bb =
    let payST  = reify (codeF2 s)
        payPT  = reify (code p)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payST (ap2 Pair payPT (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axRecPNd payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rPTV = leftT (codeF2 (RecP IfLf))
        K_rPT  = reify K_rPTV
        ext_s  = liftCompFstSnd_evalPair tagCode_axRecPNd payST
                   (ap2 Pair payPT (ap2 Pair payAT payBT)) bb
        ext_p  = liftFstSndSnd_evalPair3 tagCode_axRecPNd payST payPT
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axRecPNd payST payPT payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axRecPNd payST payPT payAT payBT bb
        kRPT   = liftKT_eval K_rPTV a bb
        ----------------------------------------------------------------
        -- Shared piece: (Pair K_rPT payST)
        recP_st  = pairOfFan_eval (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) a bb
                     K_rPT payST kRPT ext_s
        -- Shared piece: (Pair K_a2 (Pair K_pair (Pair payAT payBT)))
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        kPair_ab = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        kA2_kPair_ab = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) kPair_ab
        ----------------------------------------------------------------
        -- LHS: Pair K_a2 (Pair (Pair K_rPT payST) (Pair payPT (Pair K_a2 (Pair K_pair (Pair payAT payBT)))))
        lhs_pT_aPair = pairOfFan_eval
                         (Lift (Comp Fst (Comp Snd Snd)))
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                        Pair)
                                   Pair) Pair)
                         a bb
                         payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                         ext_p kA2_kPair_ab
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           Pair)
                      a bb
                      (ap2 Pair K_rPT payST)
                      (ap2 Pair payPT
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                      recP_st lhs_pT_aPair
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rPT payST)
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     lhs_inner
        ----------------------------------------------------------------
        -- RHS sub1: Pair K_a2 (Pair K_pair (Pair payPT (Pair K_a2 (Pair K_pair (Pair payAT payBT)))))
        sub1_pPair = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd Snd)))
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (KT K_pair))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      Pair)
                                 Pair) Pair)
                       a bb
                       payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                       ext_p kA2_kPair_ab
        sub1_kPair = pairOfConst_eval K_pairV
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       sub1_pPair
        sub1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair))
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair payPT
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                 sub1_kPair
        ----------------------------------------------------------------
        -- RHS sub2: Pair K_a2 (Pair K_pair (Pair recA recB))
        --   recA = Pair K_a2 (Pair (Pair K_rPT payST) (Pair payPT payAT))
        --   recB = Pair K_a2 (Pair (Pair K_rPT payST) (Pair payPT payBT))
        recA_pT_aT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       a bb payPT payAT ext_p ext_a
        recA_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                       a bb
                       (ap2 Pair K_rPT payST)
                       (ap2 Pair payPT payAT)
                       recP_st recA_pT_aT
        recA = pairOfConst_eval K_a2V
                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT))
                 recA_inner
        recB_pT_bT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                       a bb payPT payBT ext_p ext_b
        recB_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                       a bb
                       (ap2 Pair K_rPT payST)
                       (ap2 Pair payPT payBT)
                       recP_st recB_pT_bT
        recB = pairOfConst_eval K_a2V
                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))
                 recB_inner
        rec_AB = pairOfFan_eval
                   (Fan (Lift (KT K_a2))
                        (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                   (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))
                   recA recB
        sub2_kPair = pairOfConst_eval K_pairV
                       (Fan (Fan (Lift (KT K_a2))
                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                           (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            (Fan (Lift (KT K_a2))
                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                  (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))))
                       rec_AB
        sub2 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair))
                      (Fan (Fan (Lift (KT K_a2))
                                (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           (Fan (Lift (KT K_a2))
                                (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                              (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))))
                 sub2_kPair
        ----------------------------------------------------------------
        -- Combine sub1, sub2 -> Pair sub1 sub2
        sub1_sub2 = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                     (Fan (Lift (KT K_a2))
                                          (Fan (Lift (KT K_pair))
                                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                    Pair)
                                               Pair) Pair)
                                     Pair) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Fan (Lift (KT K_a2))
                                          (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                    Pair)
                                               Pair) Pair)
                                     (Fan (Lift (KT K_a2))
                                          (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                    Pair)
                                               Pair) Pair)
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_pair
                        (ap2 Pair payPT
                          (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                      (ap2 Pair K_a2 (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                   (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))))))
                      sub1 sub2
        rhs_st_pair = pairOfFan_eval
                        (Lift (Comp Fst Snd))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                            (Fan (Lift (KT K_a2))
                                                 (Fan (Lift (KT K_pair))
                                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                           Pair)
                                                      Pair) Pair)
                                            Pair) Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Fan (Lift (KT K_a2))
                                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                           (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                           Pair)
                                                      Pair) Pair)
                                            (Fan (Lift (KT K_a2))
                                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                           Pair)
                                                      Pair) Pair)
                                            Pair) Pair) Pair)
                             Pair)
                        a bb
                        payST
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair
                                    (ap2 Pair payPT
                                      (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair
                                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                                (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))))))
                        ext_s sub1_sub2
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_pair))
                                                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a2))
                                                   (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair payST
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair
                                   (ap2 Pair payPT
                                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair
                                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                               (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))))))))
                     rhs_st_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_pair))
                                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a2))
                                            (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair (ap2 Pair K_rPT payST)
             (ap2 Pair payPT
               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         (ap2 Pair K_a2
           (ap2 Pair payST
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair
                         (ap2 Pair payPT
                           (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                        (ap2 Pair K_a2 (ap2 Pair K_pair
                          (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                     (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))))))))
         lhsBuild rhsBuild

  thmTDispAxRecPNd : (s : Fun2) (p a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxRecPNd s p a' b')))
                       (reify (outAxRecPNd s p a' b'))))
  thmTDispAxRecPNd s p a' b' =
    let payT = reify (nd (codeF2 s) (nd (code p) (nd (code a') (code b'))))
        a    = ap2 Pair tagCode_axRecPNd payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecPNd) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecPLf payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axRecPNd payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxRecPNd refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axRecPNd payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxRecPNd refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axRecPNd payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxRecPNd refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axRecPNd payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxRecPNd refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axRecPNd payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxRecPNd refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axRecPNd payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxRecPNd refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axRecPNd payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxRecPNd refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axRecPNd payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxRecPNd refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axRecPNd payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxRecPNd refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axRecPNd payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxRecPNd refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axRecPNd payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxRecPNd refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axRecPNd payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxRecPNd refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axRecPNd payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxRecPNd refl)
        hh   = hitAtTag  (natCode tagAxRecPNd)  tagCode_axRecPNd payT b body_axRecPNd  next_axRecPNd
                  (teqEq tagAxRecPNd)
        be   = body_axRecPNd_eval s p a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans hh be))))))))))))))

  -- axRecNd z s a b : 4 args (z : Term, s : Fun2, a, b : Term); depth-4 payload.
  body_axRecNd_eval : (z : Term) (s : Fun2) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecNd
            (ap2 Pair tagCode_axRecNd
              (reify (nd (code z) (nd (codeF2 s) (nd (code a') (code b')))))) bb)
      (reify (outAxRecNd z s a' b'))))
  body_axRecNd_eval z s a' b' bb =
    let payZT  = reify (code z)
        payST  = reify (codeF2 s)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payZT (ap2 Pair payST (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axRecNd payT
        K_a1V  = tagAp1
        K_a1   = reify K_a1V
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rTV  = leftT (codeF1 (Rec O IfLf))
        K_rT   = reify K_rTV
        ext_z  = liftCompFstSnd_evalPair tagCode_axRecNd payZT
                   (ap2 Pair payST (ap2 Pair payAT payBT)) bb
        ext_s  = liftFstSndSnd_evalPair3 tagCode_axRecNd payZT payST
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axRecNd payZT payST payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axRecNd payZT payST payAT payBT bb
        ----------------------------------------------------------------
        -- Shared piece: (Pair payZT payST)
        z_s_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                     (Lift (Comp Fst (Comp Snd Snd))) a bb
                     payZT payST ext_z ext_s
        -- Shared piece: (Pair K_rT (Pair payZT payST))
        rec_zsst = pairOfConst_eval K_rTV
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payZT payST) z_s_pair
        -- Shared piece: (Pair K_a2 (Pair K_pair (Pair payAT payBT))) ( = sub1 of RHS)
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        kPair_ab = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        sub1     = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) kPair_ab
        ----------------------------------------------------------------
        -- LHS: Pair K_a1 (Pair (Pair K_rT (Pair payZT payST)) sub1)
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_rT))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                           Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_rT (ap2 Pair payZT payST))
                      (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                      rec_zsst sub1
        lhsBuild = pairOfConst_eval K_a1V
                     (Fan (Fan (Lift (KT K_rT))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair)
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair))
                                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST))
                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                     lhs_inner
        ----------------------------------------------------------------
        -- recA: Pair K_a1 (Pair (Pair K_rT (Pair payZT payST)) payAT)
        recA_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rT))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd))) Pair)
                            Pair)
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       a bb
                       (ap2 Pair K_rT (ap2 Pair payZT payST))
                       payAT
                       rec_zsst ext_a
        recA = pairOfConst_eval K_a1V
                 (Fan (Fan (Lift (KT K_rT))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                           Pair)
                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT)
                 recA_inner
        recB_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rT))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd))) Pair)
                            Pair)
                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                       a bb
                       (ap2 Pair K_rT (ap2 Pair payZT payST))
                       payBT
                       rec_zsst ext_b
        recB = pairOfConst_eval K_a1V
                 (Fan (Fan (Lift (KT K_rT))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                           Pair)
                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)
                 recB_inner
        rec_AB = pairOfFan_eval
                   (Fan (Lift (KT K_a1))
                        (Fan (Fan (Lift (KT K_rT))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair)
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             Pair) Pair)
                   (Fan (Lift (KT K_a1))
                        (Fan (Fan (Lift (KT K_rT))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair)
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                   (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))
                   recA recB
        sub2_kPair = pairOfConst_eval K_pairV
                       (Fan (Fan (Lift (KT K_a1))
                                 (Fan (Fan (Lift (KT K_rT))
                                           (Fan (Lift (Comp Fst Snd))
                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                           Pair)
                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      Pair) Pair)
                            (Fan (Lift (KT K_a1))
                                 (Fan (Fan (Lift (KT K_rT))
                                           (Fan (Lift (Comp Fst Snd))
                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                           Pair)
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                  (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)))
                       rec_AB
        sub2 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair))
                      (Fan (Fan (Lift (KT K_a1))
                                (Fan (Fan (Lift (KT K_rT))
                                          (Fan (Lift (Comp Fst Snd))
                                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                          Pair)
                                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair)
                           (Fan (Lift (KT K_a1))
                                (Fan (Fan (Lift (KT K_rT))
                                          (Fan (Lift (Comp Fst Snd))
                                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                          Pair)
                                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                              (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))))
                 sub2_kPair
        ----------------------------------------------------------------
        -- Combine sub1, sub2; then prepend payST; then K_a2.
        sub1_sub2 = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Fan (Lift (KT K_a1))
                                          (Fan (Fan (Lift (KT K_rT))
                                                    (Fan (Lift (Comp Fst Snd))
                                                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                    Pair)
                                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                               Pair) Pair)
                                     (Fan (Lift (KT K_a1))
                                          (Fan (Fan (Lift (KT K_rT))
                                                    (Fan (Lift (Comp Fst Snd))
                                                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                    Pair)
                                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                               Pair) Pair)
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                      (ap2 Pair K_a2 (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                   (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)))))
                      sub1 sub2
        rhs_st_pair = pairOfFan_eval
                        (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                            Pair) Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Fan (Lift (KT K_a1))
                                                 (Fan (Fan (Lift (KT K_rT))
                                                           (Fan (Lift (Comp Fst Snd))
                                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                           Pair)
                                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                      Pair) Pair)
                                            (Fan (Lift (KT K_a1))
                                                 (Fan (Fan (Lift (KT K_rT))
                                                           (Fan (Lift (Comp Fst Snd))
                                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                           Pair)
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair) Pair)
                                            Pair) Pair) Pair)
                             Pair)
                        a bb
                        payST
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair
                                     (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                                (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))))))
                        ext_s sub1_sub2
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a1))
                                                   (Fan (Fan (Lift (KT K_rT))
                                                             (Fan (Lift (Comp Fst Snd))
                                                                  (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                             Pair)
                                                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a1))
                                                   (Fan (Fan (Lift (KT K_rT))
                                                             (Fan (Lift (Comp Fst Snd))
                                                                  (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                             Pair)
                                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair payST
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair
                                    (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                               (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)))))))
                     rhs_st_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_rT))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_pair))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a1))
                                            (Fan (Fan (Lift (KT K_rT))
                                                      (Fan (Lift (Comp Fst Snd))
                                                           (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                      Pair)
                                                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a1))
                                            (Fan (Fan (Lift (KT K_rT))
                                                      (Fan (Lift (Comp Fst Snd))
                                                           (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                      Pair)
                                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a1
           (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST))
             (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
         (ap2 Pair K_a2
           (ap2 Pair payST
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                        (ap2 Pair K_a2 (ap2 Pair K_pair
                          (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                     (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))))))))
         lhsBuild rhsBuild

  thmTDispAxRecNd : (z : Term) (s : Fun2) (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxRecNd z s a' b')))
                       (reify (outAxRecNd z s a' b'))))
  thmTDispAxRecNd z s a' b' =
    let payT = reify (nd (code z) (nd (codeF2 s) (nd (code a') (code b'))))
        a    = ap2 Pair tagCode_axRecNd payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecNd) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecLf payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecNd payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecNd refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecNd payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecNd refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecNd payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecNd refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecNd payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecNd refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecNd payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecNd refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecNd payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecNd refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecNd payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecNd refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecNd payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecNd refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecNd payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecNd refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecNd payT b body_axZ     next_axKT
                  (teqDiff tagAxKT     tagAxRecNd refl)
        s11  = skipAtTag (natCode tagAxRecLf)  tagCode_axRecNd payT b body_axRecLf  next_axRecLf
                  (teqDiff tagAxRecLf  tagAxRecNd refl)
        hh   = hitAtTag  (natCode tagAxRecNd)  tagCode_axRecNd payT b body_axRecNd  next_axRecNd
                  (teqEq tagAxRecNd)
        be   = body_axRecNd_eval z s a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans hh be))))))))))))

  ------------------------------------------------------------------
  -- Group III non-recursive dispatch lemmas (axRefl, axEqTrans,
  -- axEqCong1, axEqCongL, axEqCongR).  The 5 recursive primitives
  -- (ruleSym, ruleTrans, cong1, congL, congR) are deferred.

  -- axRefl t : 1 arg; depth-1 payload (just code t reified).
  body_axRefl_eval : (t bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRefl (ap2 Pair tagCode_axRefl (reify (code t))) bb)
      (reify (outAxRefl t))))
  body_axRefl_eval t bb =
    let payT  = reify (code t)
        a     = ap2 Pair tagCode_axRefl payT
        snd_a = bodyLiftSndPair tagCode_axRefl payT bb
    in pairOfFan_eval (Lift Snd) (Lift Snd) a bb payT payT snd_a snd_a

  thmTDispAxRefl : (t : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxRefl t))) (reify (outAxRefl t))))
  thmTDispAxRefl t =
    let payT = reify (code t)
        a    = ap2 Pair tagCode_axRefl payT
        b    = ap2 Pair (ap1 thmT tagCode_axRefl) (ap1 thmT payT)
        e1   = dispatchOpens tagAxGoodstein payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axRefl payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxRefl refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axRefl payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxRefl refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axRefl payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxRefl refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axRefl payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxRefl refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axRefl payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxRefl refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axRefl payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxRefl refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axRefl payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxRefl refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axRefl payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxRefl refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axRefl payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxRefl refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axRefl payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxRefl refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axRefl payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxRefl refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axRefl payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxRefl refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axRefl payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxRefl refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axRefl payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxRefl refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axRefl payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxRefl refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axRefl payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxRefl refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axRefl payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxRefl refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axRefl payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxRefl refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axRefl payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxRefl refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axRefl payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxRefl refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axRefl payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxRefl refl)
        hh   = hitAtTag  (natCode tagAxRefl)      tagCode_axRefl payT b body_axRefl      next_axRefl
                  (teqEq tagAxRefl)
        be   = body_axRefl_eval t b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans hh be))))))))))))))))))))))

  -- Parametric variant of body_axRefl_eval.
  body_axRefl_eval_param : (xT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRefl (ap2 Pair tagCode_axRefl xT) bb)
      (ap2 Pair xT xT)))
  body_axRefl_eval_param xT bb =
    let payT  = xT
        a     = ap2 Pair tagCode_axRefl payT
        snd_a = bodyLiftSndPair tagCode_axRefl payT bb
    in pairOfFan_eval (Lift Snd) (Lift Snd) a bb payT payT snd_a snd_a

  -- Parametric variant of thmTDispAxRefl.
  thmTDispAxRefl_param : (xT : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair tagCode_axRefl xT))
                       (ap2 Pair xT xT)))
  thmTDispAxRefl_param xT =
    let payT = xT
        a    = ap2 Pair tagCode_axRefl payT
        b    = ap2 Pair (ap1 thmT tagCode_axRefl) (ap1 thmT payT)
        e1   = dispatchOpens tagAxGoodstein payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axRefl payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxRefl refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axRefl payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxRefl refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axRefl payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxRefl refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axRefl payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxRefl refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axRefl payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxRefl refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axRefl payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxRefl refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axRefl payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxRefl refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axRefl payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxRefl refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axRefl payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxRefl refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axRefl payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxRefl refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axRefl payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxRefl refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axRefl payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxRefl refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axRefl payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxRefl refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axRefl payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxRefl refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axRefl payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxRefl refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axRefl payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxRefl refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axRefl payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxRefl refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axRefl payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxRefl refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axRefl payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxRefl refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axRefl payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxRefl refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axRefl payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxRefl refl)
        hh   = hitAtTag  (natCode tagAxRefl)      tagCode_axRefl payT b body_axRefl      next_axRefl
                  (teqEq tagAxRefl)
        be   = body_axRefl_eval_param xT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans hh be))))))))))))))))))))))

  -- axEqTrans a b c : 3 args; depth-3 payload.
  body_axEqTrans_eval : (a' b' c' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqTrans
            (ap2 Pair tagCode_axEqTrans (reify (nd (code a') (nd (code b') (code c'))))) bb)
      (reify (outAxEqTrans a' b' c'))))
  body_axEqTrans_eval a' b' c' bb =
    let payAT  = reify (code a')
        payBT  = reify (code b')
        payCT  = reify (code c')
        payT   = ap2 Pair payAT (ap2 Pair payBT payCT)
        a      = ap2 Pair tagCode_axEqTrans payT
        K_impV = tagImp
        K_imp  = reify K_impV
        ext_a  = liftCompFstSnd_evalPair tagCode_axEqTrans payAT
                   (ap2 Pair payBT payCT) bb
        ext_b  = liftFstSndSnd_evalPair3 tagCode_axEqTrans payAT payBT payCT bb
        ext_c  = liftSndSndSnd_evalPair3 tagCode_axEqTrans payAT payBT payCT bb
        ab = pairOfFan_eval (Lift (Comp Fst Snd))
               (Lift (Comp Fst (Comp Snd Snd))) a bb payAT payBT ext_a ext_b
        ac = pairOfFan_eval (Lift (Comp Fst Snd))
               (Lift (Comp Snd (Comp Snd Snd))) a bb payAT payCT ext_a ext_c
        bc = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
               (Lift (Comp Snd (Comp Snd Snd))) a bb payBT payCT ext_b ext_c
        ac_bc = pairOfFan_eval
                  (Fan (Lift (Comp Fst Snd))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair)
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair)
                  a bb (ap2 Pair payAT payCT) (ap2 Pair payBT payCT) ac bc
        imp_acbc = pairOfConst_eval K_impV
                     (Fan (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair payAT payCT) (ap2 Pair payBT payCT))
                     ac_bc
        ab_imp = pairOfFan_eval
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   (Fan (Lift (KT K_imp))
                        (Fan (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair)
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair payAT payBT)
                   (ap2 Pair K_imp
                     (ap2 Pair (ap2 Pair payAT payCT) (ap2 Pair payBT payCT)))
                   ab imp_acbc
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair)
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair)
                        Pair) Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair K_imp
             (ap2 Pair (ap2 Pair payAT payCT) (ap2 Pair payBT payCT))))
         ab_imp

  thmTDispAxEqTrans : (a' b' c' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxEqTrans a' b' c')))
                       (reify (outAxEqTrans a' b' c'))))
  thmTDispAxEqTrans a' b' c' =
    let payT = reify (nd (code a') (nd (code b') (code c')))
        a    = ap2 Pair tagCode_axEqTrans payT
        b    = ap2 Pair (ap1 thmT tagCode_axEqTrans) (ap1 thmT payT)
        e1   = dispatchOpens tagCongR payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axEqTrans payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxEqTrans refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axEqTrans payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxEqTrans refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axEqTrans payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxEqTrans refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axEqTrans payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxEqTrans refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axEqTrans payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxEqTrans refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axEqTrans payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxEqTrans refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axEqTrans payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxEqTrans refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axEqTrans payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxEqTrans refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axEqTrans payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxEqTrans refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axEqTrans payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxEqTrans refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axEqTrans payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxEqTrans refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axEqTrans payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxEqTrans refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axEqTrans payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxEqTrans refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axEqTrans payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxEqTrans refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axEqTrans payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxEqTrans refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axEqTrans payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxEqTrans refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axEqTrans payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxEqTrans refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axEqTrans payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxEqTrans refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axEqTrans payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxEqTrans refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axEqTrans payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxEqTrans refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axEqTrans payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxEqTrans refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axEqTrans payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxEqTrans refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axEqTrans payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxEqTrans refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axEqTrans payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxEqTrans refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axEqTrans payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxEqTrans refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axEqTrans payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxEqTrans refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axEqTrans payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxEqTrans refl)
        hh   = hitAtTag  (natCode tagAxEqTrans)   tagCode_axEqTrans payT b body_axEqTrans   next_axEqTrans
                  (teqEq tagAxEqTrans)
        be   = body_axEqTrans_eval a' b' c' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans hh be))))))))))))))))))))))))))))

  -- axEqCong1 f a b : 3 args (f : Fun1, a, b : Term); depth-3 payload.
  body_axEqCong1_eval : (f : Fun1) (a' b' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqCong1
            (ap2 Pair tagCode_axEqCong1 (reify (nd (codeF1 f) (nd (code a') (code b'))))) bb)
      (reify (outAxEqCong1 f a' b'))))
  body_axEqCong1_eval f a' b' bb =
    let payFT  = reify (codeF1 f)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payT   = ap2 Pair payFT (ap2 Pair payAT payBT)
        a      = ap2 Pair tagCode_axEqCong1 payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_a1V  = tagAp1
        K_a1   = reify K_a1V
        ext_f  = liftCompFstSnd_evalPair tagCode_axEqCong1 payFT
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSnd_evalPair3 tagCode_axEqCong1 payFT payAT payBT bb
        ext_b  = liftSndSndSnd_evalPair3 tagCode_axEqCong1 payFT payAT payBT bb
        ab_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb payAT payBT ext_a ext_b
        fa_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb payFT payAT ext_f ext_a
        fb_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                    (Lift (Comp Snd (Comp Snd Snd))) a bb payFT payBT ext_f ext_b
        ka1_fa  = pairOfConst_eval K_a1V
                    (Fan (Lift (Comp Fst Snd))
                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                    a bb (ap2 Pair payFT payAT) fa_pair
        ka1_fb  = pairOfConst_eval K_a1V
                    (Fan (Lift (Comp Fst Snd))
                         (Lift (Comp Snd (Comp Snd Snd))) Pair)
                    a bb (ap2 Pair payFT payBT) fb_pair
        ka1_pair = pairOfFan_eval
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                     (Fan (Lift (KT K_a1))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair K_a1 (ap2 Pair payFT payAT))
                     (ap2 Pair K_a1 (ap2 Pair payFT payBT))
                     ka1_fa ka1_fb
        inner = pairOfFan_eval
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd Snd))) Pair)
                  (Fan (Fan (Lift (KT K_a1))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                       (Fan (Lift (KT K_a1))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                       Pair)
                  a bb
                  (ap2 Pair payAT payBT)
                  (ap2 Pair (ap2 Pair K_a1 (ap2 Pair payFT payAT))
                             (ap2 Pair K_a1 (ap2 Pair payFT payBT)))
                  ab_pair ka1_pair
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd Snd))) Pair)
              (Fan (Fan (Lift (KT K_a1))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                   (Fan (Lift (KT K_a1))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair (ap2 Pair K_a1 (ap2 Pair payFT payAT))
                      (ap2 Pair K_a1 (ap2 Pair payFT payBT))))
         inner

  thmTDispAxEqCong1 : (f : Fun1) (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxEqCong1 f a' b')))
                       (reify (outAxEqCong1 f a' b'))))
  thmTDispAxEqCong1 f a' b' =
    let payT = reify (nd (codeF1 f) (nd (code a') (code b')))
        a    = ap2 Pair tagCode_axEqCong1 payT
        b    = ap2 Pair (ap1 thmT tagCode_axEqCong1) (ap1 thmT payT)
        e1   = dispatchOpens tagAxEqTrans payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axEqCong1 payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxEqCong1 refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axEqCong1 payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxEqCong1 refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axEqCong1 payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxEqCong1 refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axEqCong1 payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxEqCong1 refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axEqCong1 payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxEqCong1 refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axEqCong1 payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxEqCong1 refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axEqCong1 payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxEqCong1 refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axEqCong1 payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxEqCong1 refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axEqCong1 payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxEqCong1 refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axEqCong1 payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxEqCong1 refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axEqCong1 payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxEqCong1 refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axEqCong1 payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxEqCong1 refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axEqCong1 payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxEqCong1 refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axEqCong1 payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxEqCong1 refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axEqCong1 payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxEqCong1 refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axEqCong1 payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxEqCong1 refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axEqCong1 payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxEqCong1 refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axEqCong1 payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxEqCong1 refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axEqCong1 payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxEqCong1 refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axEqCong1 payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxEqCong1 refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axEqCong1 payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxEqCong1 refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axEqCong1 payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxEqCong1 refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axEqCong1 payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxEqCong1 refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axEqCong1 payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxEqCong1 refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axEqCong1 payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxEqCong1 refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axEqCong1 payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxEqCong1 refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axEqCong1 payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxEqCong1 refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axEqCong1 payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxEqCong1 refl)
        hh   = hitAtTag  (natCode tagAxEqCong1)   tagCode_axEqCong1 payT b body_axEqCong1   next_axEqCong1
                  (teqEq tagAxEqCong1)
        be   = body_axEqCong1_eval f a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans hh be)))))))))))))))))))))))))))))

  -- axEqCongL g a b c : 4 args (g : Fun2, a, b, c : Term); depth-4 payload.
  body_axEqCongL_eval : (g : Fun2) (a' b' c' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqCongL
            (ap2 Pair tagCode_axEqCongL
              (reify (nd (codeF2 g) (nd (code a') (nd (code b') (code c')))))) bb)
      (reify (outAxEqCongL g a' b' c'))))
  body_axEqCongL_eval g a' b' c' bb =
    let payGT  = reify (codeF2 g)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payCT  = reify (code c')
        payT   = ap2 Pair payGT (ap2 Pair payAT (ap2 Pair payBT payCT))
        a      = ap2 Pair tagCode_axEqCongL payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        ext_g  = liftCompFstSnd_evalPair tagCode_axEqCongL payGT
                   (ap2 Pair payAT (ap2 Pair payBT payCT)) bb
        ext_a  = liftFstSndSnd_evalPair3 tagCode_axEqCongL payGT payAT
                   (ap2 Pair payBT payCT) bb
        ext_b  = liftFstSndSndSnd_evalPair4 tagCode_axEqCongL payGT payAT payBT payCT bb
        ext_c  = liftSndSndSndSnd_evalPair4 tagCode_axEqCongL payGT payAT payBT payCT bb
        ab_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                    payAT payBT ext_a ext_b
        ac_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                    payAT payCT ext_a ext_c
        bc_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                    payBT payCT ext_b ext_c
        g_ac = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                 a bb payGT (ap2 Pair payAT payCT) ext_g ac_pair
        g_bc = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                 a bb payGT (ap2 Pair payBT payCT) ext_g bc_pair
        ka2_g_ac = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payAT payCT)) g_ac
        ka2_g_bc = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payBT payCT)) g_bc
        ka2_pair = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payAT payCT)))
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payBT payCT)))
                     ka2_g_ac ka2_g_bc
        inner = pairOfFan_eval
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                  (Fan (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair) Pair)
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair) Pair)
                       Pair)
                  a bb
                  (ap2 Pair payAT payBT)
                  (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payAT payCT)))
                             (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payBT payCT))))
                  ab_pair ka2_pair
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
              (Fan (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payAT payCT)))
                      (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payBT payCT)))))
         inner

  thmTDispAxEqCongL : (g : Fun2) (a' b' c' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxEqCongL g a' b' c')))
                       (reify (outAxEqCongL g a' b' c'))))
  thmTDispAxEqCongL g a' b' c' =
    let payT = reify (nd (codeF2 g) (nd (code a') (nd (code b') (code c'))))
        a    = ap2 Pair tagCode_axEqCongL payT
        b    = ap2 Pair (ap1 thmT tagCode_axEqCongL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxEqCong1 payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axEqCongL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxEqCongL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axEqCongL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxEqCongL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axEqCongL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxEqCongL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axEqCongL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxEqCongL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axEqCongL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxEqCongL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axEqCongL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxEqCongL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axEqCongL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxEqCongL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axEqCongL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxEqCongL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axEqCongL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxEqCongL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axEqCongL payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxEqCongL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axEqCongL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxEqCongL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axEqCongL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxEqCongL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axEqCongL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxEqCongL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axEqCongL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxEqCongL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axEqCongL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxEqCongL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axEqCongL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxEqCongL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axEqCongL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxEqCongL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axEqCongL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxEqCongL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axEqCongL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxEqCongL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axEqCongL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxEqCongL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axEqCongL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxEqCongL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axEqCongL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxEqCongL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axEqCongL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxEqCongL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axEqCongL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxEqCongL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axEqCongL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxEqCongL refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axEqCongL payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxEqCongL refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axEqCongL payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxEqCongL refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axEqCongL payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxEqCongL refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axEqCongL payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxEqCongL refl)
        hh   = hitAtTag  (natCode tagAxEqCongL)   tagCode_axEqCongL payT b body_axEqCongL   next_axEqCongL
                  (teqEq tagAxEqCongL)
        be   = body_axEqCongL_eval g a' b' c' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans hh be))))))))))))))))))))))))))))))

  -- axEqCongR g a b c : 4 args; depth-4 payload.  Mirror of axEqCongL
  -- with payCT prepended (instead of appended) to payAT/payBT in the
  -- inner ap2 g _ _ codes.
  body_axEqCongR_eval : (g : Fun2) (a' b' c' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axEqCongR
            (ap2 Pair tagCode_axEqCongR
              (reify (nd (codeF2 g) (nd (code a') (nd (code b') (code c')))))) bb)
      (reify (outAxEqCongR g a' b' c'))))
  body_axEqCongR_eval g a' b' c' bb =
    let payGT  = reify (codeF2 g)
        payAT  = reify (code a')
        payBT  = reify (code b')
        payCT  = reify (code c')
        payT   = ap2 Pair payGT (ap2 Pair payAT (ap2 Pair payBT payCT))
        a      = ap2 Pair tagCode_axEqCongR payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        ext_g  = liftCompFstSnd_evalPair tagCode_axEqCongR payGT
                   (ap2 Pair payAT (ap2 Pair payBT payCT)) bb
        ext_a  = liftFstSndSnd_evalPair3 tagCode_axEqCongR payGT payAT
                   (ap2 Pair payBT payCT) bb
        ext_b  = liftFstSndSndSnd_evalPair4 tagCode_axEqCongR payGT payAT payBT payCT bb
        ext_c  = liftSndSndSndSnd_evalPair4 tagCode_axEqCongR payGT payAT payBT payCT bb
        ab_pair = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                    payAT payBT ext_a ext_b
        ca_pair = pairOfFan_eval (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                    (Lift (Comp Fst (Comp Snd Snd))) a bb
                    payCT payAT ext_c ext_a
        cb_pair = pairOfFan_eval (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                    payCT payBT ext_c ext_b
        g_ca = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                      (Lift (Comp Fst (Comp Snd Snd))) Pair)
                 a bb payGT (ap2 Pair payCT payAT) ext_g ca_pair
        g_cb = pairOfFan_eval (Lift (Comp Fst Snd))
                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                 a bb payGT (ap2 Pair payCT payBT) ext_g cb_pair
        ka2_g_ca = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payCT payAT)) g_ca
        ka2_g_cb = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair payGT (ap2 Pair payCT payBT)) g_cb
        ka2_pair = pairOfFan_eval
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair) Pair)
                     (Fan (Lift (KT K_a2))
                          (Fan (Lift (Comp Fst Snd))
                               (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payAT)))
                     (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payBT)))
                     ka2_g_ca ka2_g_cb
        inner = pairOfFan_eval
                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                  (Fan (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                 Pair) Pair)
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (Comp Fst Snd))
                                 (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                                 Pair) Pair)
                       Pair)
                  a bb
                  (ap2 Pair payAT payBT)
                  (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payAT)))
                             (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payBT))))
                  ab_pair ka2_pair
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
              (Fan (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Fst (Comp Snd Snd))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair payAT payBT)
           (ap2 Pair (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payAT)))
                      (ap2 Pair K_a2 (ap2 Pair payGT (ap2 Pair payCT payBT)))))
         inner

  thmTDispAxEqCongR : (g : Fun2) (a' b' c' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxEqCongR g a' b' c')))
                       (reify (outAxEqCongR g a' b' c'))))
  thmTDispAxEqCongR g a' b' c' =
    let payT = reify (nd (codeF2 g) (nd (code a') (nd (code b') (code c'))))
        a    = ap2 Pair tagCode_axEqCongR payT
        b    = ap2 Pair (ap1 thmT tagCode_axEqCongR) (ap1 thmT payT)
        e1   = dispatchOpens tagAxEqCongL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axEqCongR payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxEqCongR refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axEqCongR payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxEqCongR refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axEqCongR payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxEqCongR refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axEqCongR payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxEqCongR refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axEqCongR payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxEqCongR refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axEqCongR payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxEqCongR refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axEqCongR payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxEqCongR refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axEqCongR payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxEqCongR refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axEqCongR payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxEqCongR refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axEqCongR payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxEqCongR refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axEqCongR payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxEqCongR refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axEqCongR payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxEqCongR refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axEqCongR payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxEqCongR refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axEqCongR payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxEqCongR refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axEqCongR payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxEqCongR refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axEqCongR payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxEqCongR refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axEqCongR payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxEqCongR refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axEqCongR payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxEqCongR refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axEqCongR payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxEqCongR refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axEqCongR payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxEqCongR refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axEqCongR payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxEqCongR refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axEqCongR payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxEqCongR refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axEqCongR payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxEqCongR refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axEqCongR payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxEqCongR refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axEqCongR payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxEqCongR refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axEqCongR payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxEqCongR refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axEqCongR payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxEqCongR refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axEqCongR payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxEqCongR refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axEqCongR payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxEqCongR refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axEqCongR payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxEqCongR refl)
        hh   = hitAtTag  (natCode tagAxEqCongR)   tagCode_axEqCongR payT b body_axEqCongR   next_axEqCongR
                  (teqEq tagAxEqCongR)
        be   = body_axEqCongR_eval g a' b' c' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans hh be)))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Group IV non-recursive dispatch lemmas (axK, axS, axNeg,
  -- axExFalso, axContrapos).  The 4 recursive primitives
  -- (mp, ruleInst, ruleIndBT) are deferred.

  -- axK P Q : 2 args (P, Q : Formula); depth-2 payload.
  body_axK_eval : (P Q : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axK (ap2 Pair tagCode_axK (reify (nd (codeFormula P) (codeFormula Q)))) bb)
      (reify (outAxK P Q))))
  body_axK_eval P Q bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payT   = ap2 Pair payP payQ
        a      = ap2 Pair tagCode_axK payT
        K_impV = tagImp
        K_imp  = reify K_impV
        ext_p  = liftCompFstSnd_evalPair tagCode_axK payP payQ bb
        ext_q  = liftCompSndSnd_evalPair tagCode_axK payP payQ bb
        qP     = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (Comp Fst Snd))
                   a bb payQ payP ext_q ext_p
        impQP  = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Snd Snd)) (Lift (Comp Fst Snd)) Pair)
                   a bb (ap2 Pair payQ payP) qP
        midRHS = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Snd Snd))
                             (Lift (Comp Fst Snd)) Pair) Pair)
                   a bb payP (ap2 Pair K_imp (ap2 Pair payQ payP))
                   ext_p impQP
    in pairOfConst_eval K_impV
         (Fan (Lift (Comp Fst Snd))
              (Fan (Lift (KT K_imp))
                   (Fan (Lift (Comp Snd Snd))
                        (Lift (Comp Fst Snd)) Pair) Pair) Pair)
         a bb
         (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payP)))
         midRHS

  thmTDispAxK : (P Q : Formula) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxK P Q))) (reify (outAxK P Q))))
  thmTDispAxK P Q =
    let payT = reify (nd (codeFormula P) (codeFormula Q))
        a    = ap2 Pair tagCode_axK payT
        b    = ap2 Pair (ap1 thmT tagCode_axK) (ap1 thmT payT)
        e1   = dispatchOpens tagAxEqCongR payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axK payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxK refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axK payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxK refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axK payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxK refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axK payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxK refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axK payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxK refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axK payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxK refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axK payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxK refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axK payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxK refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axK payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxK refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axK payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxK refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axK payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxK refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axK payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxK refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axK payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxK refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axK payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxK refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axK payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxK refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axK payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxK refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axK payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxK refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axK payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxK refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axK payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxK refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axK payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxK refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axK payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxK refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axK payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxK refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axK payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxK refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axK payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxK refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axK payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxK refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axK payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxK refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axK payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxK refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axK payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxK refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axK payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxK refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axK payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxK refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axK payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxK refl)
        hh   = hitAtTag  (natCode tagAxK)         tagCode_axK payT b body_axK         next_axK
                  (teqEq tagAxK)
        be   = body_axK_eval P Q b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans hh be))))))))))))))))))))))))))))))))

  -- axS P Q R : 3 args; depth-3 payload.
  body_axS_eval : (P Q R : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axS (ap2 Pair tagCode_axS
                       (reify (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R))))) bb)
      (reify (outAxS P Q R))))
  body_axS_eval P Q R bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payR   = reify (codeFormula R)
        payT   = ap2 Pair payP (ap2 Pair payQ payR)
        a      = ap2 Pair tagCode_axS payT
        K_impV = tagImp
        K_imp  = reify K_impV
        ext_p  = liftCompFstSnd_evalPair tagCode_axS payP (ap2 Pair payQ payR) bb
        ext_q  = liftFstSndSnd_evalPair3 tagCode_axS payP payQ payR bb
        ext_r  = liftSndSndSnd_evalPair3 tagCode_axS payP payQ payR bb
        -- A = Pair K_imp (Pair payP (Pair K_imp (Pair payQ payR)))
        qr     = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd Snd))) a bb payQ payR ext_q ext_r
        impQR  = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payQ payR) qr
        pImpQR = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                   a bb payP (ap2 Pair K_imp (ap2 Pair payQ payR))
                   ext_p impQR
        bigA   = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Fst Snd))
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair)
                   a bb (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payR))) pImpQR
        -- B = Pair K_imp (Pair (Pair K_imp (Pair payP payQ)) (Pair K_imp (Pair payP payR)))
        pq     = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) a bb payP payQ ext_p ext_q
        impPQ  = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payP payQ) pq
        pr     = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Snd (Comp Snd Snd))) a bb payP payR ext_p ext_r
        impPR  = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Snd (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payP payR) pr
        impPQ_PR = pairOfFan_eval
                     (Fan (Lift (KT K_imp))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                     (Fan (Lift (KT K_imp))
                          (Fan (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                     a bb
                     (ap2 Pair K_imp (ap2 Pair payP payQ))
                     (ap2 Pair K_imp (ap2 Pair payP payR))
                     impPQ impPR
        bigB   = pairOfConst_eval K_impV
                   (Fan (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
                              (ap2 Pair K_imp (ap2 Pair payP payR)))
                   impPQ_PR
        ab     = pairOfFan_eval
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Fst Snd))
                             (Fan (Lift (KT K_imp))
                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                       (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair) Pair)
                   (Fan (Lift (KT K_imp))
                        (Fan (Fan (Lift (KT K_imp))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                             (Fan (Lift (KT K_imp))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_imp (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payR))))
                   (ap2 Pair K_imp (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
                                              (ap2 Pair K_imp (ap2 Pair payP payR))))
                   bigA bigB
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (KT K_imp))
                   (Fan (Lift (Comp Fst Snd))
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair) Pair) Pair)
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Fst (Comp Snd Snd))) Pair) Pair)
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Fst Snd))
                                  (Lift (Comp Snd (Comp Snd Snd))) Pair) Pair)
                        Pair) Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP (ap2 Pair K_imp (ap2 Pair payQ payR))))
                    (ap2 Pair K_imp (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
                                                (ap2 Pair K_imp (ap2 Pair payP payR)))))
         ab

  thmTDispAxS : (P Q R : Formula) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxS P Q R))) (reify (outAxS P Q R))))
  thmTDispAxS P Q R =
    let payT = reify (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R)))
        a    = ap2 Pair tagCode_axS payT
        b    = ap2 Pair (ap1 thmT tagCode_axS) (ap1 thmT payT)
        e1   = dispatchOpens tagAxK payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axS payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxS refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axS payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxS refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axS payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxS refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axS payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxS refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axS payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxS refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axS payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxS refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axS payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxS refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axS payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxS refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axS payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxS refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axS payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxS refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axS payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxS refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axS payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxS refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axS payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxS refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axS payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxS refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axS payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxS refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axS payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxS refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axS payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxS refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axS payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxS refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axS payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxS refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axS payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxS refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axS payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxS refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axS payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxS refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axS payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxS refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axS payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxS refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axS payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxS refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axS payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxS refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axS payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxS refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axS payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxS refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axS payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxS refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axS payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxS refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axS payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxS refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axS payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxS refl)
        hh   = hitAtTag  (natCode tagAxS)         tagCode_axS payT b body_axS         next_axS
                  (teqEq tagAxS)
        be   = body_axS_eval P Q R b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans hh be)))))))))))))))))))))))))))))))))

  -- axNeg P Q : 2 args; depth-2 payload.
  body_axNeg_eval : (P Q : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axNeg (ap2 Pair tagCode_axNeg (reify (nd (codeFormula P) (codeFormula Q)))) bb)
      (reify (outAxNeg P Q))))
  body_axNeg_eval P Q bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payT   = ap2 Pair payP payQ
        a      = ap2 Pair tagCode_axNeg payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_negV = tagNeg
        K_neg  = reify K_negV
        ext_p  = liftCompFstSnd_evalPair tagCode_axNeg payP payQ bb
        ext_q  = liftCompSndSnd_evalPair tagCode_axNeg payP payQ bb
        qP     = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (Comp Fst Snd))
                   a bb payQ payP ext_q ext_p
        impQP  = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Snd Snd)) (Lift (Comp Fst Snd)) Pair)
                   a bb (ap2 Pair payQ payP) qP
        negQ   = pairOfConst_eval K_negV (Lift (Comp Snd Snd)) a bb payQ ext_q
        negQ_impQP = pairOfFan_eval
                       (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                       (Fan (Lift (KT K_imp))
                            (Fan (Lift (Comp Snd Snd))
                                 (Lift (Comp Fst Snd)) Pair) Pair)
                       a bb
                       (ap2 Pair K_neg payQ)
                       (ap2 Pair K_imp (ap2 Pair payQ payP))
                       negQ impQP
        impNegQ = pairOfConst_eval K_impV
                    (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                         (Fan (Lift (KT K_imp))
                              (Fan (Lift (Comp Snd Snd))
                                   (Lift (Comp Fst Snd)) Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_neg payQ)
                               (ap2 Pair K_imp (ap2 Pair payQ payP)))
                    negQ_impQP
        negP   = pairOfConst_eval K_negV (Lift (Comp Fst Snd)) a bb payP ext_p
        negP_imp = pairOfFan_eval
                     (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                     (Fan (Lift (KT K_imp))
                          (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                               (Fan (Lift (KT K_imp))
                                    (Fan (Lift (Comp Snd Snd))
                                         (Lift (Comp Fst Snd)) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_neg payP)
                     (ap2 Pair K_imp
                       (ap2 Pair (ap2 Pair K_neg payQ)
                                  (ap2 Pair K_imp (ap2 Pair payQ payP))))
                     negP impNegQ
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                        (Fan (Lift (KT K_imp))
                             (Fan (Lift (Comp Snd Snd))
                                  (Lift (Comp Fst Snd)) Pair) Pair)
                        Pair) Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair K_neg payP)
           (ap2 Pair K_imp
             (ap2 Pair (ap2 Pair K_neg payQ)
                        (ap2 Pair K_imp (ap2 Pair payQ payP)))))
         negP_imp

  thmTDispAxNeg : (P Q : Formula) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxNeg P Q))) (reify (outAxNeg P Q))))
  thmTDispAxNeg P Q =
    let payT = reify (nd (codeFormula P) (codeFormula Q))
        a    = ap2 Pair tagCode_axNeg payT
        b    = ap2 Pair (ap1 thmT tagCode_axNeg) (ap1 thmT payT)
        e1   = dispatchOpens tagAxS payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axNeg payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxNeg refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axNeg payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxNeg refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axNeg payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxNeg refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axNeg payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxNeg refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axNeg payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxNeg refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axNeg payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxNeg refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axNeg payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxNeg refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axNeg payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxNeg refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axNeg payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxNeg refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axNeg payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxNeg refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axNeg payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxNeg refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axNeg payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxNeg refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axNeg payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxNeg refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axNeg payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxNeg refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axNeg payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxNeg refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axNeg payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxNeg refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axNeg payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxNeg refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axNeg payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxNeg refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axNeg payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxNeg refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axNeg payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxNeg refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axNeg payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxNeg refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axNeg payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxNeg refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axNeg payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxNeg refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axNeg payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxNeg refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axNeg payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxNeg refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axNeg payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxNeg refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axNeg payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxNeg refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axNeg payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxNeg refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axNeg payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxNeg refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axNeg payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxNeg refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axNeg payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxNeg refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axNeg payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxNeg refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axNeg payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxNeg refl)
        hh   = hitAtTag  (natCode tagAxNeg)       tagCode_axNeg payT b body_axNeg       next_axNeg
                  (teqEq tagAxNeg)
        be   = body_axNeg_eval P Q b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans hh be))))))))))))))))))))))))))))))))))

  -- axExFalso P Q : 2 args; depth-2 payload.
  body_axExFalso_eval : (P Q : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axExFalso
            (ap2 Pair tagCode_axExFalso (reify (nd (codeFormula P) (codeFormula Q)))) bb)
      (reify (outAxExFalso P Q))))
  body_axExFalso_eval P Q bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payT   = ap2 Pair payP payQ
        a      = ap2 Pair tagCode_axExFalso payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_negV = tagNeg
        K_neg  = reify K_negV
        ext_p  = liftCompFstSnd_evalPair tagCode_axExFalso payP payQ bb
        ext_q  = liftCompSndSnd_evalPair tagCode_axExFalso payP payQ bb
        negP   = pairOfConst_eval K_negV (Lift (Comp Fst Snd)) a bb payP ext_p
        negP_q = pairOfFan_eval
                   (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                   (Lift (Comp Snd Snd))
                   a bb (ap2 Pair K_neg payP) payQ negP ext_q
        impNegPQ = pairOfConst_eval K_impV
                     (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                          (Lift (Comp Snd Snd)) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_neg payP) payQ)
                     negP_q
        p_imp = pairOfFan_eval (Lift (Comp Fst Snd))
                  (Fan (Lift (KT K_imp))
                       (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                            (Lift (Comp Snd Snd)) Pair) Pair)
                  a bb payP
                  (ap2 Pair K_imp (ap2 Pair (ap2 Pair K_neg payP) payQ))
                  ext_p impNegPQ
    in pairOfConst_eval K_impV
         (Fan (Lift (Comp Fst Snd))
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                        (Lift (Comp Snd Snd)) Pair) Pair) Pair)
         a bb
         (ap2 Pair payP
           (ap2 Pair K_imp (ap2 Pair (ap2 Pair K_neg payP) payQ)))
         p_imp

  thmTDispAxExFalso : (P Q : Formula) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxExFalso P Q))) (reify (outAxExFalso P Q))))
  thmTDispAxExFalso P Q =
    let payT = reify (nd (codeFormula P) (codeFormula Q))
        a    = ap2 Pair tagCode_axExFalso payT
        b    = ap2 Pair (ap1 thmT tagCode_axExFalso) (ap1 thmT payT)
        e1   = dispatchOpens tagAxNeg payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axExFalso payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxExFalso refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axExFalso payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxExFalso refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axExFalso payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxExFalso refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axExFalso payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxExFalso refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axExFalso payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxExFalso refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axExFalso payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxExFalso refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axExFalso payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxExFalso refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axExFalso payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxExFalso refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axExFalso payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxExFalso refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axExFalso payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxExFalso refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axExFalso payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxExFalso refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axExFalso payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxExFalso refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axExFalso payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxExFalso refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axExFalso payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxExFalso refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axExFalso payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxExFalso refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axExFalso payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxExFalso refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axExFalso payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxExFalso refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axExFalso payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxExFalso refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axExFalso payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxExFalso refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axExFalso payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxExFalso refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axExFalso payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxExFalso refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axExFalso payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxExFalso refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axExFalso payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxExFalso refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axExFalso payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxExFalso refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axExFalso payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxExFalso refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axExFalso payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxExFalso refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axExFalso payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxExFalso refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axExFalso payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxExFalso refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axExFalso payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxExFalso refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axExFalso payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxExFalso refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axExFalso payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxExFalso refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axExFalso payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxExFalso refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axExFalso payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxExFalso refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axExFalso payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxExFalso refl)
        hh   = hitAtTag  (natCode tagAxExFalso)   tagCode_axExFalso payT b body_axExFalso   next_axExFalso
                  (teqEq tagAxExFalso)
        be   = body_axExFalso_eval P Q b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans hh be)))))))))))))))))))))))))))))))))))

  -- axContrapos P Q : 2 args; depth-2 payload.
  body_axContrapos_eval : (P Q : Formula) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axContrapos
            (ap2 Pair tagCode_axContrapos (reify (nd (codeFormula P) (codeFormula Q)))) bb)
      (reify (outAxContrapos P Q))))
  body_axContrapos_eval P Q bb =
    let payP   = reify (codeFormula P)
        payQ   = reify (codeFormula Q)
        payT   = ap2 Pair payP payQ
        a      = ap2 Pair tagCode_axContrapos payT
        K_impV = tagImp
        K_imp  = reify K_impV
        K_negV = tagNeg
        K_neg  = reify K_negV
        ext_p  = liftCompFstSnd_evalPair tagCode_axContrapos payP payQ bb
        ext_q  = liftCompSndSnd_evalPair tagCode_axContrapos payP payQ bb
        pq     = pairOfFan_eval (Lift (Comp Fst Snd)) (Lift (Comp Snd Snd))
                   a bb payP payQ ext_p ext_q
        impPQ  = pairOfConst_eval K_impV
                   (Fan (Lift (Comp Fst Snd)) (Lift (Comp Snd Snd)) Pair)
                   a bb (ap2 Pair payP payQ) pq
        negQ   = pairOfConst_eval K_negV (Lift (Comp Snd Snd)) a bb payQ ext_q
        negP   = pairOfConst_eval K_negV (Lift (Comp Fst Snd)) a bb payP ext_p
        negQ_negP = pairOfFan_eval
                      (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                      (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                      a bb
                      (ap2 Pair K_neg payQ) (ap2 Pair K_neg payP)
                      negQ negP
        impNegQ_negP = pairOfConst_eval K_impV
                         (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                              (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                              Pair)
                         a bb
                         (ap2 Pair (ap2 Pair K_neg payQ) (ap2 Pair K_neg payP))
                         negQ_negP
        ab     = pairOfFan_eval
                   (Fan (Lift (KT K_imp))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Snd Snd)) Pair) Pair)
                   (Fan (Lift (KT K_imp))
                        (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                             (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_imp (ap2 Pair payP payQ))
                   (ap2 Pair K_imp
                     (ap2 Pair (ap2 Pair K_neg payQ) (ap2 Pair K_neg payP)))
                   impPQ impNegQ_negP
    in pairOfConst_eval K_impV
         (Fan (Fan (Lift (KT K_imp))
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Snd Snd)) Pair) Pair)
              (Fan (Lift (KT K_imp))
                   (Fan (Fan (Lift (KT K_neg)) (Lift (Comp Snd Snd)) Pair)
                        (Fan (Lift (KT K_neg)) (Lift (Comp Fst Snd)) Pair)
                        Pair) Pair)
              Pair)
         a bb
         (ap2 Pair (ap2 Pair K_imp (ap2 Pair payP payQ))
           (ap2 Pair K_imp
             (ap2 Pair (ap2 Pair K_neg payQ) (ap2 Pair K_neg payP))))
         ab

  thmTDispAxContrapos : (P Q : Formula) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxContrapos P Q))) (reify (outAxContrapos P Q))))
  thmTDispAxContrapos P Q =
    let payT = reify (nd (codeFormula P) (codeFormula Q))
        a    = ap2 Pair tagCode_axContrapos payT
        b    = ap2 Pair (ap1 thmT tagCode_axContrapos) (ap1 thmT payT)
        e1   = dispatchOpens tagAxExFalso payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axContrapos payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxContrapos refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axContrapos payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxContrapos refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axContrapos payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxContrapos refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axContrapos payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxContrapos refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axContrapos payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxContrapos refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axContrapos payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxContrapos refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axContrapos payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxContrapos refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axContrapos payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxContrapos refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axContrapos payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxContrapos refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axContrapos payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagAxContrapos refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axContrapos payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxContrapos refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axContrapos payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxContrapos refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axContrapos payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxContrapos refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axContrapos payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxContrapos refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axContrapos payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxContrapos refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axContrapos payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxContrapos refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axContrapos payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxContrapos refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axContrapos payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxContrapos refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axContrapos payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxContrapos refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axContrapos payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxContrapos refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axContrapos payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxContrapos refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axContrapos payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxContrapos refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axContrapos payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxContrapos refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axContrapos payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxContrapos refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axContrapos payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxContrapos refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axContrapos payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxContrapos refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axContrapos payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxContrapos refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axContrapos payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxContrapos refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axContrapos payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxContrapos refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axContrapos payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxContrapos refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axContrapos payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxContrapos refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axContrapos payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxContrapos refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axContrapos payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxContrapos refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axContrapos payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxContrapos refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axContrapos payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxContrapos refl)
        hh   = hitAtTag  (natCode tagAxContrapos) tagCode_axContrapos payT b body_axContrapos next_axContrapos
                  (teqEq tagAxContrapos)
        be   = body_axContrapos_eval P Q b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35 (ruleTrans hh be))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Recursive primitives.
  --
  -- These differ structurally from the non-recursive cases: the body
  -- output depends on  Snd b  (the recursion result), not just on the
  -- payload  Snd a .  The dispatch lemma takes IH proofs about
  --  thmT(reify y_i)  and uses them to bridge from the body's purely
  -- structural output (in terms of  Snd b ) to the desired conclusion.

  -- Helper: ap2 (Post (Comp X (Comp Snd Snd)) Pair) a b = ap1 X (ap1 Snd b).
  -- Used for both Snd-of-Snd-b and Fst-of-Snd-b extractors.
  postSndBody_eval : (X : Fun1) (a b : Term) ->
    Deriv (atomic (eqn (ap2 (Post (Comp X (Comp Snd Snd)) Pair) a b)
                       (ap1 X (ap1 Snd b))))
  postSndBody_eval X a b =
    let e1 : Deriv (atomic (eqn (ap2 (Post (Comp X (Comp Snd Snd)) Pair) a b)
                                 (ap1 (Comp X (Comp Snd Snd)) (ap2 Pair a b))))
        e1 = axPost (Comp X (Comp Snd Snd)) Pair a b
        e2 : Deriv (atomic (eqn (ap1 (Comp X (Comp Snd Snd)) (ap2 Pair a b))
                                 (ap1 X (ap1 (Comp Snd Snd) (ap2 Pair a b)))))
        e2 = axComp X (Comp Snd Snd) (ap2 Pair a b)
        e3a : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap2 Pair a b))
                                  (ap1 Snd (ap1 Snd (ap2 Pair a b)))))
        e3a = axComp Snd Snd (ap2 Pair a b)
        e3b : Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
        e3b = axSnd a b
        e3c : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair a b))) (ap1 Snd b)))
        e3c = cong1 Snd e3b
        e3 : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap2 Pair a b)) (ap1 Snd b)))
        e3 = ruleTrans e3a e3c
        e4 : Deriv (atomic (eqn (ap1 X (ap1 (Comp Snd Snd) (ap2 Pair a b)))
                                 (ap1 X (ap1 Snd b))))
        e4 = cong1 X e3
    in ruleTrans e1 (ruleTrans e2 e4)

  -- ruleSym y_h : RECURSIVE.
  --   IH: thmT(reify y_h) = reify (codeFormula (atomic (eqn t u))).
  --   Goal: thmT(reify (encRuleSym y_h)) = reify (outRuleSym t u)
  --                                     = reify (codeFormula (atomic (eqn u t))).
  body_ruleSym_eval : (t u : Term) (y_h : Tree) (bb : Term) ->
    -- Pre-extracted IH: ap1 Snd bb = reify (code (eqn t u)).
    Deriv (atomic (eqn (ap1 Snd bb)
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn
      (ap2 body_ruleSym (ap2 Pair tagCode_ruleSym (reify y_h)) bb)
      (reify (outRuleSym t u))))
  body_ruleSym_eval t u y_h bb sndB_eq =
    let payT      = reify y_h
        payTcoded = reify (code t)
        payUcoded = reify (code u)
        a         = ap2 Pair tagCode_ruleSym payT
        -- Step 1: ap2 body a bb = Pair (ap2 X a bb) (ap2 Y a bb)  via axFan
        e_fan : Deriv (atomic (eqn (ap2 body_ruleSym a bb)
                                    (ap2 Pair
                                      (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                                      (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb))))
        e_fan = axFan (Post (Comp Snd (Comp Snd Snd)) Pair)
                       (Post (Comp Fst (Comp Snd Snd)) Pair) Pair a bb
        -- Step 2: extractors evaluate to Snd(Snd bb) and Fst(Snd bb).
        e_X : Deriv (atomic (eqn (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                                  (ap1 Snd (ap1 Snd bb))))
        e_X = postSndBody_eval Snd a bb
        e_Y : Deriv (atomic (eqn (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb)
                                  (ap1 Fst (ap1 Snd bb))))
        e_Y = postSndBody_eval Fst a bb
        -- Step 3: Snd bb = Pair payTcoded payUcoded  (via sndB_eq;
        -- reify(codeFormula (atomic (eqn t u))) reduces to Pair payTcoded payUcoded
        -- since codeFormula (atomic e) = codeEqn e = nd (code l) (code r)).
        e_sndsnd_a : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                         (ap1 Snd (ap2 Pair payTcoded payUcoded))))
        e_sndsnd_a = cong1 Snd sndB_eq
        e_sndsnd_b : Deriv (atomic (eqn (ap1 Snd (ap2 Pair payTcoded payUcoded)) payUcoded))
        e_sndsnd_b = axSnd payTcoded payUcoded
        e_sndsnd : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) payUcoded))
        e_sndsnd = ruleTrans e_sndsnd_a e_sndsnd_b
        e_fstsnd_a : Deriv (atomic (eqn (ap1 Fst (ap1 Snd bb))
                                         (ap1 Fst (ap2 Pair payTcoded payUcoded))))
        e_fstsnd_a = cong1 Fst sndB_eq
        e_fstsnd_b : Deriv (atomic (eqn (ap1 Fst (ap2 Pair payTcoded payUcoded)) payTcoded))
        e_fstsnd_b = axFst payTcoded payUcoded
        e_fstsnd : Deriv (atomic (eqn (ap1 Fst (ap1 Snd bb)) payTcoded))
        e_fstsnd = ruleTrans e_fstsnd_a e_fstsnd_b
        -- Step 4: ap2 X a bb = payUcoded; ap2 Y a bb = payTcoded.
        e_X_final : Deriv (atomic (eqn (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                                        payUcoded))
        e_X_final = ruleTrans e_X e_sndsnd
        e_Y_final : Deriv (atomic (eqn (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb)
                                        payTcoded))
        e_Y_final = ruleTrans e_Y e_fstsnd
        -- Step 5: Pair (ap2 X a bb) (ap2 Y a bb) = Pair payUcoded payTcoded.
        e_pair_l : Deriv (atomic (eqn
          (ap2 Pair (ap2 (Post (Comp Snd (Comp Snd Snd)) Pair) a bb)
                     (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb))
          (ap2 Pair payUcoded
                     (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb))))
        e_pair_l = congL Pair (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb) e_X_final
        e_pair_r : Deriv (atomic (eqn
          (ap2 Pair payUcoded (ap2 (Post (Comp Fst (Comp Snd Snd)) Pair) a bb))
          (ap2 Pair payUcoded payTcoded)))
        e_pair_r = congR Pair payUcoded e_Y_final
    in ruleTrans e_fan (ruleTrans e_pair_l e_pair_r)

  thmTDispRuleSym : (t u : Term) (y_h : Tree) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encRuleSym y_h)))
                       (reify (outRuleSym t u))))
  thmTDispRuleSym t u y_h d_h =
    let payT = reify y_h
        a    = ap2 Pair tagCode_ruleSym payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleSym) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRefl payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleSym payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleSym refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleSym payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleSym refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleSym payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleSym refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleSym payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleSym refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleSym payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleSym refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleSym payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleSym refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleSym payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleSym refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleSym payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleSym refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleSym payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleSym refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleSym payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagRuleSym refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleSym payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleSym refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleSym payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleSym refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleSym payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleSym refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleSym payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleSym refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleSym payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleSym refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleSym payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleSym refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleSym payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleSym refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleSym payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleSym refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleSym payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleSym refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleSym payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleSym refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleSym payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleSym refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleSym payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleSym refl)
        hh   = hitAtTag  (natCode tagRuleSym)     tagCode_ruleSym payT b body_ruleSym     next_ruleSym
                  (teqEq tagRuleSym)
        -- Bridge: Snd b = ap1 thmT payT  (via axSnd), then apply IH d_h.
        sndB_unfold : Deriv (atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleSym) (ap1 thmT payT)
        sndB_eq : Deriv (atomic (eqn (ap1 Snd b)
                                      (reify (codeFormula (atomic (eqn t u))))))
        sndB_eq = ruleTrans sndB_unfold d_h
        be = body_ruleSym_eval t u y_h b sndB_eq
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22
       (ruleTrans hh be)))))))))))))))))))))))

  ------------------------------------------------------------------
  -- ruleIndBT P v1 v2 y_base y_step : RECURSIVE (2 sub-proofs), but
  -- the conclusion is just  P , whose code is stored explicitly in
  -- the encoding payload at  Fst(Snd a) .  So the body does no IH
  -- application; the IHs are phantom in the body but required in the
  -- dispatch signature for compatibility with  encode .

  body_ruleIndBT_eval : (P : Formula) (v1 v2 : Nat)
                        (y_base y_step : Tree) (bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_ruleIndBT
            (ap2 Pair tagCode_ruleIndBT
                  (reify (nd (codeFormula P)
                              (nd (code (var v1))
                                  (nd (code (var v2))
                                      (nd y_base y_step))))))
            bb)
      (reify (outRuleIndBT P))))
  body_ruleIndBT_eval P v1 v2 y_base y_step bb =
    let restT : Term
        restT = reify (nd (code (var v1))
                          (nd (code (var v2))
                              (nd y_base y_step)))
    in liftCompFstSnd_evalPair tagCode_ruleIndBT
                               (reify (codeFormula P))
                               restT bb

  thmTDispRuleIndBT : (P : Formula) (v1 v2 : Nat) (y_base y_step : Tree) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_base))
                       (reify (codeFormula (substF zero O P))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_step))
                       (reify (codeFormula
                               ((substF zero (var v1) P) imp
                                ((substF zero (var v2) P) imp
                                 (substF zero (ap2 Pair (var v1) (var v2)) P))))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encRuleIndBT P v1 v2 y_base y_step)))
                       (reify (outRuleIndBT P))))
  thmTDispRuleIndBT P v1 v2 y_base y_step _ _ =
    let payT = reify (nd (codeFormula P)
                         (nd (code (var v1))
                             (nd (code (var v2))
                                 (nd y_base y_step))))
        a    = ap2 Pair tagCode_ruleIndBT payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleIndBT) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleInst payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleIndBT payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleIndBT refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleIndBT payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleIndBT refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleIndBT payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleIndBT refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleIndBT payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleIndBT refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleIndBT payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleIndBT refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleIndBT payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleIndBT refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleIndBT payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleIndBT refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleIndBT payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleIndBT refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleIndBT payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleIndBT refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleIndBT payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagRuleIndBT refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleIndBT payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleIndBT refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleIndBT payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleIndBT refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleIndBT payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleIndBT refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleIndBT payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleIndBT refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleIndBT payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleIndBT refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleIndBT payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleIndBT refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleIndBT payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleIndBT refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleIndBT payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleIndBT refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleIndBT payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleIndBT refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleIndBT payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleIndBT refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleIndBT payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleIndBT refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleIndBT payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleIndBT refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleIndBT payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleIndBT refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_ruleIndBT payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagRuleIndBT refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_ruleIndBT payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagRuleIndBT refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_ruleIndBT payT b body_congL       next_congL
                  (teqDiff tagCongL       tagRuleIndBT refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_ruleIndBT payT b body_congR       next_congR
                  (teqDiff tagCongR       tagRuleIndBT refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_ruleIndBT payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagRuleIndBT refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_ruleIndBT payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagRuleIndBT refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_ruleIndBT payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagRuleIndBT refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_ruleIndBT payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagRuleIndBT refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_ruleIndBT payT b body_axK         next_axK
                  (teqDiff tagAxK         tagRuleIndBT refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_ruleIndBT payT b body_axS         next_axS
                  (teqDiff tagAxS         tagRuleIndBT refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_ruleIndBT payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagRuleIndBT refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_ruleIndBT payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagRuleIndBT refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_ruleIndBT payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagRuleIndBT refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_ruleIndBT payT b body_mp          next_mp
                  (teqDiff tagMp          tagRuleIndBT refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_ruleIndBT payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagRuleIndBT refl)
        hh   = hitAtTag  (natCode tagRuleIndBT)   tagCode_ruleIndBT payT b body_ruleIndBT   next_ruleIndBT
                  (teqEq tagRuleIndBT)
        be   = body_ruleIndBT_eval P v1 v2 y_base y_step b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38
       (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))

  -- Parametric variant of body_ruleIndBT_eval (Theorem 12 / Parts/{Rec,RecP,IfLf,TreeEq}.agda).
  -- y_base_T, y_step_T : Term parameters in place of reify y_base, reify y_step.
  body_ruleIndBT_eval_param : (P : Formula) (v1 v2 : Nat)
                              (y_base_T y_step_T bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_ruleIndBT
            (ap2 Pair tagCode_ruleIndBT
                  (ap2 Pair (reify (codeFormula P))
                    (ap2 Pair (reify (code (var v1)))
                      (ap2 Pair (reify (code (var v2)))
                        (ap2 Pair y_base_T y_step_T)))))
            bb)
      (reify (codeFormula P))))
  body_ruleIndBT_eval_param P v1 v2 y_base_T y_step_T bb =
    let restT : Term
        restT = ap2 Pair (reify (code (var v1)))
                   (ap2 Pair (reify (code (var v2)))
                     (ap2 Pair y_base_T y_step_T))
    in liftCompFstSnd_evalPair tagCode_ruleIndBT
                               (reify (codeFormula P))
                               restT bb

  -- Parametric variant of thmTDispRuleIndBT.
  thmTDispRuleIndBT_param : (P : Formula) (v1 v2 : Nat) (y_base_T y_step_T : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleIndBT
                          (ap2 Pair (reify (codeFormula P))
                            (ap2 Pair (reify (code (var v1)))
                              (ap2 Pair (reify (code (var v2)))
                                (ap2 Pair y_base_T y_step_T))))))
      (reify (codeFormula P))))
  thmTDispRuleIndBT_param P v1 v2 y_base_T y_step_T =
    let payT = ap2 Pair (reify (codeFormula P))
                  (ap2 Pair (reify (code (var v1)))
                    (ap2 Pair (reify (code (var v2)))
                      (ap2 Pair y_base_T y_step_T)))
        a    = ap2 Pair tagCode_ruleIndBT payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleIndBT) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleInst payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleIndBT payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleIndBT refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleIndBT payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleIndBT refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleIndBT payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleIndBT refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleIndBT payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleIndBT refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleIndBT payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleIndBT refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleIndBT payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleIndBT refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleIndBT payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleIndBT refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleIndBT payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleIndBT refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleIndBT payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleIndBT refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleIndBT payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagRuleIndBT refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleIndBT payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleIndBT refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleIndBT payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleIndBT refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleIndBT payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleIndBT refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleIndBT payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleIndBT refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleIndBT payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleIndBT refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleIndBT payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleIndBT refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleIndBT payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleIndBT refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleIndBT payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleIndBT refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleIndBT payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleIndBT refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleIndBT payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleIndBT refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleIndBT payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleIndBT refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleIndBT payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleIndBT refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleIndBT payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleIndBT refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_ruleIndBT payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagRuleIndBT refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_ruleIndBT payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagRuleIndBT refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_ruleIndBT payT b body_congL       next_congL
                  (teqDiff tagCongL       tagRuleIndBT refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_ruleIndBT payT b body_congR       next_congR
                  (teqDiff tagCongR       tagRuleIndBT refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_ruleIndBT payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagRuleIndBT refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_ruleIndBT payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagRuleIndBT refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_ruleIndBT payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagRuleIndBT refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_ruleIndBT payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagRuleIndBT refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_ruleIndBT payT b body_axK         next_axK
                  (teqDiff tagAxK         tagRuleIndBT refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_ruleIndBT payT b body_axS         next_axS
                  (teqDiff tagAxS         tagRuleIndBT refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_ruleIndBT payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagRuleIndBT refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_ruleIndBT payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagRuleIndBT refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_ruleIndBT payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagRuleIndBT refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_ruleIndBT payT b body_mp          next_mp
                  (teqDiff tagMp          tagRuleIndBT refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_ruleIndBT payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagRuleIndBT refl)
        hh   = hitAtTag  (natCode tagRuleIndBT)   tagCode_ruleIndBT payT b body_ruleIndBT   next_ruleIndBT
                  (teqEq tagRuleIndBT)
        be   = body_ruleIndBT_eval_param P v1 v2 y_base_T y_step_T b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38
       (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- 4 safe-default-axiom dispatches (axFstLf, axSndLf, axIfLfLL,
  -- axIfLfNL).  Each cascade skips ALL 39 existing tags (axI..ruleIndBT)
  -- plus any earlier safe-default tags, then hits at its own tag.

  -- axFstLf : 0 args; output = reify outAxFstLf, closed constant.
  body_axFstLf_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFstLf (ap2 Pair tagCode_axFstLf O) b)
      (reify outAxFstLf)))
  body_axFstLf_eval b =
    liftKT_eval outAxFstLf (ap2 Pair tagCode_axFstLf O) b

  thmTDispAxFstLf :
    Deriv (atomic (eqn (ap1 thmT (reify encAxFstLf)) (reify outAxFstLf)))
  thmTDispAxFstLf =
    let payT = O
        a    = ap2 Pair tagCode_axFstLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axFstLf) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleIndBT payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axFstLf payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxFstLf refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axFstLf payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxFstLf refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axFstLf payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxFstLf refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axFstLf payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxFstLf refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axFstLf payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxFstLf refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axFstLf payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxFstLf refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axFstLf payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxFstLf refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axFstLf payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxFstLf refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axFstLf payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxFstLf refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axFstLf payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxFstLf refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axFstLf payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxFstLf refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axFstLf payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxFstLf refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axFstLf payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxFstLf refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axFstLf payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxFstLf refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axFstLf payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxFstLf refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axFstLf payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxFstLf refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axFstLf payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxFstLf refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axFstLf payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxFstLf refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axFstLf payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxFstLf refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axFstLf payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxFstLf refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axFstLf payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxFstLf refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axFstLf payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxFstLf refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axFstLf payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxFstLf refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axFstLf payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxFstLf refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axFstLf payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxFstLf refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axFstLf payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxFstLf refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axFstLf payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxFstLf refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axFstLf payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxFstLf refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axFstLf payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxFstLf refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axFstLf payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxFstLf refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axFstLf payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxFstLf refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axFstLf payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxFstLf refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axFstLf payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxFstLf refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axFstLf payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxFstLf refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axFstLf payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxFstLf refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axFstLf payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxFstLf refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axFstLf payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxFstLf refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axFstLf payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxFstLf refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axFstLf payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxFstLf refl)
        hh   = hitAtTag  (natCode tagAxFstLf)     tagCode_axFstLf payT b body_axFstLf     next_axFstLf
                  (teqEq tagAxFstLf)
        be   = body_axFstLf_eval b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))

  -- Parametric variant of body_axFstLf_eval.  The body ignores its
  -- second component, so we simply allow an arbitrary payT parameter.
  body_axFstLf_eval_param : (payT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axFstLf (ap2 Pair tagCode_axFstLf payT) bb)
      (reify outAxFstLf)))
  body_axFstLf_eval_param payT bb =
    liftKT_eval outAxFstLf (ap2 Pair tagCode_axFstLf payT) bb

  -- Parametric variant of thmTDispAxFstLf.  Allows any payload.
  thmTDispAxFstLf_param : (payT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axFstLf payT))
      (reify outAxFstLf)))
  thmTDispAxFstLf_param payT =
    let a    = ap2 Pair tagCode_axFstLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axFstLf) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleIndBT payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axFstLf payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxFstLf refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axFstLf payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxFstLf refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axFstLf payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxFstLf refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axFstLf payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxFstLf refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axFstLf payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxFstLf refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axFstLf payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxFstLf refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axFstLf payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxFstLf refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axFstLf payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxFstLf refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axFstLf payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxFstLf refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axFstLf payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxFstLf refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axFstLf payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxFstLf refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axFstLf payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxFstLf refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axFstLf payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxFstLf refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axFstLf payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxFstLf refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axFstLf payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxFstLf refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axFstLf payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxFstLf refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axFstLf payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxFstLf refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axFstLf payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxFstLf refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axFstLf payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxFstLf refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axFstLf payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxFstLf refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axFstLf payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxFstLf refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axFstLf payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxFstLf refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axFstLf payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxFstLf refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axFstLf payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxFstLf refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axFstLf payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxFstLf refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axFstLf payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxFstLf refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axFstLf payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxFstLf refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axFstLf payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxFstLf refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axFstLf payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxFstLf refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axFstLf payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxFstLf refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axFstLf payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxFstLf refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axFstLf payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxFstLf refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axFstLf payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxFstLf refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axFstLf payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxFstLf refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axFstLf payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxFstLf refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axFstLf payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxFstLf refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axFstLf payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxFstLf refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axFstLf payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxFstLf refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axFstLf payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxFstLf refl)
        hh   = hitAtTag  (natCode tagAxFstLf)     tagCode_axFstLf payT b body_axFstLf     next_axFstLf
                  (teqEq tagAxFstLf)
        be   = body_axFstLf_eval_param payT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))

  -- axSndLf : 0 args; closed output.
  body_axSndLf_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axSndLf (ap2 Pair tagCode_axSndLf O) b)
      (reify outAxSndLf)))
  body_axSndLf_eval b =
    liftKT_eval outAxSndLf (ap2 Pair tagCode_axSndLf O) b

  thmTDispAxSndLf :
    Deriv (atomic (eqn (ap1 thmT (reify encAxSndLf)) (reify outAxSndLf)))
  thmTDispAxSndLf =
    let payT = O
        a    = ap2 Pair tagCode_axSndLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axSndLf) (ap1 thmT payT)
        e1   = dispatchOpens tagAxFstLf payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axSndLf payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxSndLf refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axSndLf payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxSndLf refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axSndLf payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxSndLf refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axSndLf payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxSndLf refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axSndLf payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxSndLf refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axSndLf payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxSndLf refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axSndLf payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxSndLf refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axSndLf payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxSndLf refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axSndLf payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxSndLf refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axSndLf payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxSndLf refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axSndLf payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxSndLf refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axSndLf payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxSndLf refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axSndLf payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxSndLf refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axSndLf payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxSndLf refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axSndLf payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxSndLf refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axSndLf payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxSndLf refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axSndLf payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxSndLf refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axSndLf payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxSndLf refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axSndLf payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxSndLf refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axSndLf payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxSndLf refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axSndLf payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxSndLf refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axSndLf payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxSndLf refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axSndLf payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxSndLf refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axSndLf payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxSndLf refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axSndLf payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxSndLf refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axSndLf payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxSndLf refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axSndLf payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxSndLf refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axSndLf payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxSndLf refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axSndLf payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxSndLf refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axSndLf payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxSndLf refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axSndLf payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxSndLf refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axSndLf payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxSndLf refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axSndLf payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxSndLf refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axSndLf payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxSndLf refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axSndLf payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxSndLf refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axSndLf payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxSndLf refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axSndLf payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxSndLf refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axSndLf payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxSndLf refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axSndLf payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxSndLf refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axSndLf payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxSndLf refl)
        hh   = hitAtTag  (natCode tagAxSndLf)     tagCode_axSndLf payT b body_axSndLf     next_axSndLf
                  (teqEq tagAxSndLf)
        be   = body_axSndLf_eval b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))))

  -- Parametric variant of body_axSndLf_eval.
  body_axSndLf_eval_param : (payT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axSndLf (ap2 Pair tagCode_axSndLf payT) bb)
      (reify outAxSndLf)))
  body_axSndLf_eval_param payT bb =
    liftKT_eval outAxSndLf (ap2 Pair tagCode_axSndLf payT) bb

  -- Parametric variant of thmTDispAxSndLf.
  thmTDispAxSndLf_param : (payT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axSndLf payT))
      (reify outAxSndLf)))
  thmTDispAxSndLf_param payT =
    let a    = ap2 Pair tagCode_axSndLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axSndLf) (ap1 thmT payT)
        e1   = dispatchOpens tagAxFstLf payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axSndLf payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxSndLf refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axSndLf payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxSndLf refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axSndLf payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxSndLf refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axSndLf payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxSndLf refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axSndLf payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxSndLf refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axSndLf payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxSndLf refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axSndLf payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxSndLf refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axSndLf payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxSndLf refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axSndLf payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxSndLf refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axSndLf payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxSndLf refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axSndLf payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxSndLf refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axSndLf payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxSndLf refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axSndLf payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxSndLf refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axSndLf payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxSndLf refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axSndLf payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxSndLf refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axSndLf payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxSndLf refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axSndLf payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxSndLf refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axSndLf payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxSndLf refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axSndLf payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxSndLf refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axSndLf payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxSndLf refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axSndLf payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxSndLf refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axSndLf payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxSndLf refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axSndLf payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxSndLf refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axSndLf payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxSndLf refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axSndLf payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxSndLf refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axSndLf payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxSndLf refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axSndLf payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxSndLf refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axSndLf payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxSndLf refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axSndLf payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxSndLf refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axSndLf payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxSndLf refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axSndLf payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxSndLf refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axSndLf payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxSndLf refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axSndLf payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxSndLf refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axSndLf payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxSndLf refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axSndLf payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxSndLf refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axSndLf payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxSndLf refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axSndLf payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxSndLf refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axSndLf payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxSndLf refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axSndLf payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxSndLf refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axSndLf payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxSndLf refl)
        hh   = hitAtTag  (natCode tagAxSndLf)     tagCode_axSndLf payT b body_axSndLf     next_axSndLf
                  (teqEq tagAxSndLf)
        be   = body_axSndLf_eval_param payT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))))

  -- axIfLfLL : 0 args; closed output.
  body_axIfLfLL_eval : (b : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfLL (ap2 Pair tagCode_axIfLfLL O) b)
      (reify outAxIfLfLL)))
  body_axIfLfLL_eval b =
    liftKT_eval outAxIfLfLL (ap2 Pair tagCode_axIfLfLL O) b

  thmTDispAxIfLfLL :
    Deriv (atomic (eqn (ap1 thmT (reify encAxIfLfLL)) (reify outAxIfLfLL)))
  thmTDispAxIfLfLL =
    let payT = O
        a    = ap2 Pair tagCode_axIfLfLL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfLL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxSndLf payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axIfLfLL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxIfLfLL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axIfLfLL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxIfLfLL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axIfLfLL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxIfLfLL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axIfLfLL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxIfLfLL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axIfLfLL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxIfLfLL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axIfLfLL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxIfLfLL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axIfLfLL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxIfLfLL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axIfLfLL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxIfLfLL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axIfLfLL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxIfLfLL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axIfLfLL payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxIfLfLL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axIfLfLL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxIfLfLL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axIfLfLL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxIfLfLL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axIfLfLL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxIfLfLL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axIfLfLL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxIfLfLL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axIfLfLL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxIfLfLL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axIfLfLL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxIfLfLL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axIfLfLL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxIfLfLL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axIfLfLL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxIfLfLL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axIfLfLL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxIfLfLL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axIfLfLL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxIfLfLL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axIfLfLL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxIfLfLL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axIfLfLL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxIfLfLL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axIfLfLL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxIfLfLL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axIfLfLL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxIfLfLL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axIfLfLL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxIfLfLL refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axIfLfLL payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxIfLfLL refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axIfLfLL payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxIfLfLL refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axIfLfLL payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxIfLfLL refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axIfLfLL payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxIfLfLL refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axIfLfLL payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxIfLfLL refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axIfLfLL payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxIfLfLL refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axIfLfLL payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxIfLfLL refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axIfLfLL payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxIfLfLL refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axIfLfLL payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxIfLfLL refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axIfLfLL payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxIfLfLL refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axIfLfLL payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxIfLfLL refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axIfLfLL payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxIfLfLL refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axIfLfLL payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxIfLfLL refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axIfLfLL payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxIfLfLL refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axIfLfLL payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxIfLfLL refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axIfLfLL payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxIfLfLL refl)
        hh   = hitAtTag  (natCode tagAxIfLfLL)    tagCode_axIfLfLL payT b body_axIfLfLL    next_axIfLfLL
                  (teqEq tagAxIfLfLL)
        be   = body_axIfLfLL_eval b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))))

  -- Parametric variant of body_axIfLfLL_eval.
  body_axIfLfLL_eval_param : (payT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfLL (ap2 Pair tagCode_axIfLfLL payT) bb)
      (reify outAxIfLfLL)))
  body_axIfLfLL_eval_param payT bb =
    liftKT_eval outAxIfLfLL (ap2 Pair tagCode_axIfLfLL payT) bb

  -- Parametric variant of thmTDispAxIfLfLL.
  thmTDispAxIfLfLL_param : (payT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axIfLfLL payT))
      (reify outAxIfLfLL)))
  thmTDispAxIfLfLL_param payT =
    let a    = ap2 Pair tagCode_axIfLfLL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfLL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxSndLf payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axIfLfLL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxIfLfLL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axIfLfLL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxIfLfLL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axIfLfLL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxIfLfLL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axIfLfLL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxIfLfLL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axIfLfLL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxIfLfLL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axIfLfLL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxIfLfLL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axIfLfLL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxIfLfLL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axIfLfLL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxIfLfLL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axIfLfLL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxIfLfLL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axIfLfLL payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxIfLfLL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axIfLfLL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxIfLfLL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axIfLfLL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxIfLfLL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axIfLfLL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxIfLfLL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axIfLfLL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxIfLfLL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axIfLfLL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxIfLfLL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axIfLfLL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxIfLfLL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axIfLfLL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxIfLfLL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axIfLfLL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxIfLfLL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axIfLfLL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxIfLfLL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axIfLfLL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxIfLfLL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axIfLfLL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxIfLfLL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axIfLfLL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxIfLfLL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axIfLfLL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxIfLfLL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axIfLfLL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxIfLfLL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axIfLfLL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxIfLfLL refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axIfLfLL payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxIfLfLL refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axIfLfLL payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxIfLfLL refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axIfLfLL payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxIfLfLL refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axIfLfLL payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxIfLfLL refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axIfLfLL payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxIfLfLL refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axIfLfLL payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxIfLfLL refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axIfLfLL payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxIfLfLL refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axIfLfLL payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxIfLfLL refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axIfLfLL payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxIfLfLL refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axIfLfLL payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxIfLfLL refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axIfLfLL payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxIfLfLL refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axIfLfLL payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxIfLfLL refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axIfLfLL payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxIfLfLL refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axIfLfLL payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxIfLfLL refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axIfLfLL payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxIfLfLL refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axIfLfLL payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxIfLfLL refl)
        hh   = hitAtTag  (natCode tagAxIfLfLL)    tagCode_axIfLfLL payT b body_axIfLfLL    next_axIfLfLL
                  (teqEq tagAxIfLfLL)
        be   = body_axIfLfLL_eval_param payT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))))

  -- axIfLfNL x y : 2 args; depth-2 payload.
  body_axIfLfNL_eval : (x' y' bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfNL
            (ap2 Pair tagCode_axIfLfNL (reify (nd (code x') (code y')))) bb)
      (reify (outAxIfLfNL x' y'))))
  body_axIfLfNL_eval x' y' bb =
    let payX  = reify (code x')
        payY  = reify (code y')
        payT  = ap2 Pair payX payY
        a     = ap2 Pair tagCode_axIfLfNL payT
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        snd_a : Deriv (atomic (eqn (ap2 (Lift Snd) a bb) payT))
        snd_a = bodyLiftSndPair tagCode_axIfLfNL payT bb
        l1 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l2 = pairOfConst_eval K_a2V
                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                (ap2 Pair K_pair payT) l1
        l3 = pairOfFan_eval
                (Fan (Lift (KT K_a2)) (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                (Lift (KT O)) a bb
                (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O
                l2 (liftKT_eval lf a bb)
        l4 = pairOfConst_eval K_ifLfV
                (Fan (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair)) (Lift Snd) Pair)
                          Pair)
                     (Lift (KT O))
                     Pair)
                a bb
                (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O)
                l3
        l5 = pairOfConst_eval K_a2V
                (Fan (Lift (KT K_ifLf))
                     (Fan (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair)) (Lift Snd) Pair)
                               Pair)
                          (Lift (KT O))
                          Pair)
                     Pair)
                a bb
                (ap2 Pair K_ifLf (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O))
                l4
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair)
                             Pair)
                        (Lift (KT O))
                        Pair)
                   Pair)
              Pair)
         (Lift (KT O)) a bb
         (ap2 Pair K_a2
              (ap2 Pair K_ifLf
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O)))
         O
         l5 (liftKT_eval lf a bb)

  thmTDispAxIfLfNL : (x' y' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxIfLfNL x' y')))
                       (reify (outAxIfLfNL x' y'))))
  thmTDispAxIfLfNL x' y' =
    let payT = reify (nd (code x') (code y'))
        a    = ap2 Pair tagCode_axIfLfNL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfNL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfLL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axIfLfNL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxIfLfNL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axIfLfNL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxIfLfNL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axIfLfNL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxIfLfNL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axIfLfNL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxIfLfNL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axIfLfNL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxIfLfNL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axIfLfNL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxIfLfNL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axIfLfNL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxIfLfNL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axIfLfNL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxIfLfNL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axIfLfNL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxIfLfNL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axIfLfNL payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxIfLfNL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axIfLfNL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxIfLfNL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axIfLfNL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxIfLfNL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axIfLfNL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxIfLfNL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axIfLfNL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxIfLfNL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axIfLfNL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxIfLfNL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axIfLfNL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxIfLfNL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axIfLfNL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxIfLfNL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axIfLfNL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxIfLfNL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axIfLfNL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxIfLfNL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axIfLfNL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxIfLfNL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axIfLfNL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxIfLfNL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axIfLfNL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxIfLfNL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axIfLfNL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxIfLfNL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axIfLfNL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxIfLfNL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axIfLfNL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxIfLfNL refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axIfLfNL payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxIfLfNL refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axIfLfNL payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxIfLfNL refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axIfLfNL payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxIfLfNL refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axIfLfNL payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxIfLfNL refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axIfLfNL payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxIfLfNL refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axIfLfNL payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxIfLfNL refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axIfLfNL payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxIfLfNL refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axIfLfNL payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxIfLfNL refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axIfLfNL payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxIfLfNL refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axIfLfNL payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxIfLfNL refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axIfLfNL payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxIfLfNL refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axIfLfNL payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxIfLfNL refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axIfLfNL payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxIfLfNL refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axIfLfNL payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxIfLfNL refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axIfLfNL payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxIfLfNL refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axIfLfNL payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxIfLfNL refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_axIfLfNL payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagAxIfLfNL refl)
        hh   = hitAtTag  (natCode tagAxIfLfNL)    tagCode_axIfLfNL payT b body_axIfLfNL    next_axIfLfNL
                  (teqEq tagAxIfLfNL)
        be   = body_axIfLfNL_eval x' y' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))))))

  -- Parametric variant of body_axIfLfNL_eval (Theorem 12 / Parts/IfLf.agda).
  body_axIfLfNL_eval_param : (xT yT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axIfLfNL (ap2 Pair tagCode_axIfLfNL (ap2 Pair xT yT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair xT yT)))
                      O)))
        O)))
  body_axIfLfNL_eval_param xT yT bb =
    let payX  = xT
        payY  = yT
        payT  = ap2 Pair payX payY
        a     = ap2 Pair tagCode_axIfLfNL payT
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        snd_a : Deriv (atomic (eqn (ap2 (Lift Snd) a bb) payT))
        snd_a = bodyLiftSndPair tagCode_axIfLfNL payT bb
        l1 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l2 = pairOfConst_eval K_a2V
                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                (ap2 Pair K_pair payT) l1
        l3 = pairOfFan_eval
                (Fan (Lift (KT K_a2)) (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                (Lift (KT O)) a bb
                (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O
                l2 (liftKT_eval lf a bb)
        l4 = pairOfConst_eval K_ifLfV
                (Fan (Fan (Lift (KT K_a2))
                          (Fan (Lift (KT K_pair)) (Lift Snd) Pair)
                          Pair)
                     (Lift (KT O))
                     Pair)
                a bb
                (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O)
                l3
        l5 = pairOfConst_eval K_a2V
                (Fan (Lift (KT K_ifLf))
                     (Fan (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair)) (Lift Snd) Pair)
                               Pair)
                          (Lift (KT O))
                          Pair)
                     Pair)
                a bb
                (ap2 Pair K_ifLf (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O))
                l4
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair)
                             Pair)
                        (Lift (KT O))
                        Pair)
                   Pair)
              Pair)
         (Lift (KT O)) a bb
         (ap2 Pair K_a2
              (ap2 Pair K_ifLf
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) O)))
         O
         l5 (liftKT_eval lf a bb)

  -- Parametric variant of thmTDispAxIfLfNL.
  thmTDispAxIfLfNL_param : (xT yT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axIfLfNL (ap2 Pair xT yT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair xT yT)))
                      O)))
        O)))
  thmTDispAxIfLfNL_param xT yT =
    let payT = ap2 Pair xT yT
        a    = ap2 Pair tagCode_axIfLfNL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfNL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfLL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axIfLfNL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxIfLfNL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axIfLfNL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxIfLfNL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axIfLfNL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxIfLfNL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axIfLfNL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxIfLfNL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axIfLfNL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxIfLfNL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axIfLfNL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxIfLfNL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axIfLfNL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxIfLfNL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axIfLfNL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxIfLfNL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axIfLfNL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxIfLfNL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axIfLfNL payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxIfLfNL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_axIfLfNL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagAxIfLfNL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_axIfLfNL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagAxIfLfNL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_axIfLfNL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagAxIfLfNL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_axIfLfNL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagAxIfLfNL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axIfLfNL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxIfLfNL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axIfLfNL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxIfLfNL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axIfLfNL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxIfLfNL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axIfLfNL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxIfLfNL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axIfLfNL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxIfLfNL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axIfLfNL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxIfLfNL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axIfLfNL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxIfLfNL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axIfLfNL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxIfLfNL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axIfLfNL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxIfLfNL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axIfLfNL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxIfLfNL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axIfLfNL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxIfLfNL refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axIfLfNL payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxIfLfNL refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axIfLfNL payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxIfLfNL refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axIfLfNL payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxIfLfNL refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axIfLfNL payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxIfLfNL refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axIfLfNL payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxIfLfNL refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axIfLfNL payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxIfLfNL refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axIfLfNL payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxIfLfNL refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axIfLfNL payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxIfLfNL refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axIfLfNL payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxIfLfNL refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axIfLfNL payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxIfLfNL refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axIfLfNL payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxIfLfNL refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axIfLfNL payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxIfLfNL refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axIfLfNL payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxIfLfNL refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axIfLfNL payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxIfLfNL refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axIfLfNL payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxIfLfNL refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axIfLfNL payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxIfLfNL refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_axIfLfNL payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagAxIfLfNL refl)
        hh   = hitAtTag  (natCode tagAxIfLfNL)    tagCode_axIfLfNL payT b body_axIfLfNL    next_axIfLfNL
                  (teqEq tagAxIfLfNL)
        be   = body_axIfLfNL_eval_param xT yT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Inner-pair passthrough.  Given a head-shape proof
  --   Fst(reify y1) = Pair O y1'
  -- (which holds for every encoder result, since encX y_h =
  -- nd (natCode (suc tagX_pred)) ... reifies to Pair (Pair O ...) ...),
  -- we can derive
  --   thmT (reify (nd y1 y2)) = Pair (thmT (reify y1)) (thmT (reify y2)) .
  -- This unblocks recursive primitives whose payloads have inner-pair
  -- shape (mp, ruleTrans, cong1, congL, congR, ruleInst).

  -- Accepts any  Pair x' y'  shape, not just  Pair O y' .  Existing
  -- callers pass  x' = O  (sub-encoding head shape from encodeRich);
  -- ruleInst's first-level distribution uses  fstReifyCodeVar  whose
  -- shape has  x' = reify (nd (nd lf lf) lf) , so the implicit x'
  -- makes the lemma reusable.
  thmTDistrib : (y1 y2 : Tree) {x' : Term} (y1' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y1)) (ap2 Pair x' y1'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (nd y1 y2)))
                       (ap2 Pair (ap1 thmT (reify y1)) (ap1 thmT (reify y2)))))
  thmTDistrib y1 y2 {x'} y1' shape =
    let a : Term
        a = ap2 Pair (reify y1) (reify y2)
        b' : Term
        b' = ap2 Pair (ap1 thmT (reify y1)) (ap1 thmT (reify y2))
        e1 : Deriv (atomic (eqn (ap1 thmT a) (ap2 stepProto a b')))
        e1 = axRecNd O stepProto (reify y1) (reify y2)
        f1 : Deriv (atomic (eqn (ap1 Fst a) (reify y1)))
        f1 = axFst (reify y1) (reify y2)
        f2 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) (ap1 Fst (reify y1))))
        f2 = cong1 Fst f1
        f3 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) (ap2 Pair x' y1')))
        f3 = ruleTrans f2 shape
        e2 : Deriv (atomic (eqn (ap2 stepProto a b') b'))
        e2 = stepProto_else a b' x' y1' f3
    in ruleTrans e1 e2

  -- Parametric variant of thmTDistrib (Theorem 12 / recursive Parts files).
  thmTDistrib_param : (y1T y2T : Term) {x' : Term} (y1' : Term) ->
    Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair y1T y2T))
                       (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
  thmTDistrib_param y1T y2T {x'} y1' shape =
    let a : Term
        a = ap2 Pair y1T y2T
        b' : Term
        b' = ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)
        e1 = axRecNd O stepProto y1T y2T
        f1 = axFst y1T y2T
        f2 = cong1 Fst f1
        f3 = ruleTrans f2 shape
        e2 = stepProto_else a b' x' y1' f3
    in ruleTrans e1 e2

  ------------------------------------------------------------------
  -- mp y1 y2 : RECURSIVE (2 sub-proofs).  IH1 gives the imp formula
  -- code; the body extracts payQ = Snd(Snd(Fst(Snd b))) once Snd b
  -- has been distributed.

  body_mp_eval : (P Q : Formula) (y1 y2 : Tree) (bb : Term) ->
    -- distH: Snd bb = Pair (thmT (reify y1)) (thmT (reify y2)) .
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify y1)) (ap1 thmT (reify y2))))) ->
    -- IH d1: thmT (reify y1) = reify (codeFormula (P imp Q)) .
    Deriv (atomic (eqn (ap1 thmT (reify y1)) (reify (codeFormula (P imp Q))))) ->
    Deriv (atomic (eqn
      (ap2 body_mp (ap2 Pair tagCode_mp (reify (nd y1 y2))) bb)
      (reify (outMp Q))))
  body_mp_eval P Q y1 y2 bb distH d1 =
    let tj1 : Term
        tj1 = ap1 thmT (reify y1)
        tj2 : Term
        tj2 = ap1 thmT (reify y2)
        a : Term
        a = ap2 Pair tagCode_mp (reify (nd y1 y2))
        pT : Term
        pT = reify (codeFormula P)
        qT : Term
        qT = reify (codeFormula Q)
        K_imp : Term
        K_imp = reify tagImp
        X : Fun1
        X = Comp Snd (Comp Snd Fst)
        e1 : Deriv (atomic (eqn (ap2 body_mp a bb) (ap1 X (ap1 Snd bb))))
        e1 = postSndBody_eval X a bb
        e2 : Deriv (atomic (eqn (ap1 X (ap1 Snd bb))
                                 (ap1 X (ap2 Pair tj1 tj2))))
        e2 = cong1 X distH
        e3a : Deriv (atomic (eqn (ap1 X (ap2 Pair tj1 tj2))
                                  (ap1 Snd (ap1 (Comp Snd Fst) (ap2 Pair tj1 tj2)))))
        e3a = axComp Snd (Comp Snd Fst) (ap2 Pair tj1 tj2)
        e3b : Deriv (atomic (eqn (ap1 (Comp Snd Fst) (ap2 Pair tj1 tj2))
                                  (ap1 Snd (ap1 Fst (ap2 Pair tj1 tj2)))))
        e3b = axComp Snd Fst (ap2 Pair tj1 tj2)
        e3c : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tj1 tj2)) tj1))
        e3c = axFst tj1 tj2
        e3d : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap2 Pair tj1 tj2)))
                                  (ap1 Snd tj1)))
        e3d = cong1 Snd e3c
        e3e : Deriv (atomic (eqn (ap1 (Comp Snd Fst) (ap2 Pair tj1 tj2))
                                  (ap1 Snd tj1)))
        e3e = ruleTrans e3b e3d
        e3f : Deriv (atomic (eqn (ap1 Snd (ap1 (Comp Snd Fst) (ap2 Pair tj1 tj2)))
                                  (ap1 Snd (ap1 Snd tj1))))
        e3f = cong1 Snd e3e
        e3 : Deriv (atomic (eqn (ap1 X (ap2 Pair tj1 tj2))
                                 (ap1 Snd (ap1 Snd tj1))))
        e3 = ruleTrans e3a e3f
        e4a : Deriv (atomic (eqn (ap1 Snd tj1)
                                  (ap1 Snd (reify (codeFormula (P imp Q))))))
        e4a = cong1 Snd d1
        e4b : Deriv (atomic (eqn (ap1 Snd (reify (codeFormula (P imp Q))))
                                  (ap2 Pair pT qT)))
        e4b = axSnd K_imp (ap2 Pair pT qT)
        e4 : Deriv (atomic (eqn (ap1 Snd tj1) (ap2 Pair pT qT)))
        e4 = ruleTrans e4a e4b
        e5a : Deriv (atomic (eqn (ap1 Snd (ap1 Snd tj1))
                                  (ap1 Snd (ap2 Pair pT qT))))
        e5a = cong1 Snd e4
        e5b : Deriv (atomic (eqn (ap1 Snd (ap2 Pair pT qT)) qT))
        e5b = axSnd pT qT
        e5 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd tj1)) qT))
        e5 = ruleTrans e5a e5b
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e5))

  thmTDispMp : (P Q : Formula) (y1 y2 : Tree) (y1' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y1)) (ap2 Pair O y1'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y1))
                       (reify (codeFormula (P imp Q))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y2))
                       (reify (codeFormula P)))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encMp y1 y2)))
                       (reify (outMp Q))))
  thmTDispMp P Q y1 y2 y1' shape d1 _ =
    let payT = reify (nd y1 y2)
        a    = ap2 Pair tagCode_mp payT
        b    = ap2 Pair (ap1 thmT tagCode_mp) (ap1 thmT payT)
        e1   = dispatchOpens tagAxContrapos payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_mp payT b body_axI         next_axI
                  (teqDiff tagAxI         tagMp refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_mp payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagMp refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_mp payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagMp refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_mp payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagMp refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_mp payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagMp refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_mp payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagMp refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_mp payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagMp refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_mp payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagMp refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_mp payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagMp refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_mp payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagMp refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_mp payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagMp refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_mp payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagMp refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_mp payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagMp refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_mp payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagMp refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_mp payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagMp refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_mp payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagMp refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_mp payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagMp refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_mp payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagMp refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_mp payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagMp refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_mp payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagMp refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_mp payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagMp refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_mp payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagMp refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_mp payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagMp refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_mp payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagMp refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_mp payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagMp refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_mp payT b body_congL       next_congL
                  (teqDiff tagCongL       tagMp refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_mp payT b body_congR       next_congR
                  (teqDiff tagCongR       tagMp refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_mp payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagMp refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_mp payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagMp refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_mp payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagMp refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_mp payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagMp refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_mp payT b body_axK         next_axK
                  (teqDiff tagAxK         tagMp refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_mp payT b body_axS         next_axS
                  (teqDiff tagAxS         tagMp refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_mp payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagMp refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_mp payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagMp refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_mp payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagMp refl)
        hh   = hitAtTag  (natCode tagMp)          tagCode_mp payT b body_mp          next_mp
                  (teqEq tagMp)
        sndB_unfold : Deriv (atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndB_unfold = axSnd (ap1 thmT tagCode_mp) (ap1 thmT payT)
        distrib : Deriv (atomic (eqn (ap1 thmT payT)
                                      (ap2 Pair (ap1 thmT (reify y1))
                                                (ap1 thmT (reify y2)))))
        distrib = thmTDistrib y1 y2 y1' shape
        distH : Deriv (atomic (eqn (ap1 Snd b)
                                    (ap2 Pair (ap1 thmT (reify y1))
                                              (ap1 thmT (reify y2)))))
        distH = ruleTrans sndB_unfold distrib
        be = body_mp_eval P Q y1 y2 b distH d1
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- ruleTrans y1 y2 : RECURSIVE (2 sub-proofs).  Output is
  -- reify(codeFormula(atomic (eqn t v))) = Pair payT_r payV_r.
  -- After distribution Snd b = Pair (thmT y1_r) (thmT y2_r) , the
  -- body extracts payT_r = Fst(Fst(Snd b)) (via IH1) and
  -- payV_r = Snd(Snd(Snd b)) (via IH2) and pairs them.

  body_ruleTrans_eval : (t u v : Term) (y1 y2 : Tree) (bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify y1)) (ap1 thmT (reify y2))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y1))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y2))
                       (reify (codeFormula (atomic (eqn u v)))))) ->
    Deriv (atomic (eqn
      (ap2 body_ruleTrans (ap2 Pair tagCode_ruleTrans (reify (nd y1 y2))) bb)
      (reify (outRuleTrans t v))))
  body_ruleTrans_eval t u v y1 y2 bb distH d1 d2 =
    let tj1 : Term
        tj1 = ap1 thmT (reify y1)
        tj2 : Term
        tj2 = ap1 thmT (reify y2)
        a : Term
        a = ap2 Pair tagCode_ruleTrans (reify (nd y1 y2))
        payT_r : Term
        payT_r = reify (code t)
        payU_r : Term
        payU_r = reify (code u)
        payV_r : Term
        payV_r = reify (code v)
        e1L : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp Fst Fst) (ap1 Snd bb))))
        e1L = postSndBody_eval (Comp Fst Fst) a bb
        e2L : Deriv (atomic (eqn (ap1 (Comp Fst Fst) (ap1 Snd bb))
                                  (ap1 (Comp Fst Fst) (ap2 Pair tj1 tj2))))
        e2L = cong1 (Comp Fst Fst) distH
        e3aL : Deriv (atomic (eqn (ap1 (Comp Fst Fst) (ap2 Pair tj1 tj2))
                                   (ap1 Fst (ap1 Fst (ap2 Pair tj1 tj2)))))
        e3aL = axComp Fst Fst (ap2 Pair tj1 tj2)
        e3bL : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tj1 tj2)) tj1))
        e3bL = axFst tj1 tj2
        e3cL : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tj1 tj2)))
                                   (ap1 Fst tj1)))
        e3cL = cong1 Fst e3bL
        e3L : Deriv (atomic (eqn (ap1 (Comp Fst Fst) (ap2 Pair tj1 tj2))
                                  (ap1 Fst tj1)))
        e3L = ruleTrans e3aL e3cL
        e4aL : Deriv (atomic (eqn (ap1 Fst tj1)
                                   (ap1 Fst (reify (codeFormula (atomic (eqn t u)))))))
        e4aL = cong1 Fst d1
        e4bL : Deriv (atomic (eqn (ap1 Fst (reify (codeFormula (atomic (eqn t u)))))
                                   payT_r))
        e4bL = axFst payT_r payU_r
        e4L : Deriv (atomic (eqn (ap1 Fst tj1) payT_r))
        e4L = ruleTrans e4aL e4bL
        eL : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair) a bb)
          payT_r))
        eL = ruleTrans e1L (ruleTrans e2L (ruleTrans e3L e4L))
        e1R : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp Snd Snd) (ap1 Snd bb))))
        e1R = postSndBody_eval (Comp Snd Snd) a bb
        e2R : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap1 Snd bb))
                                  (ap1 (Comp Snd Snd) (ap2 Pair tj1 tj2))))
        e2R = cong1 (Comp Snd Snd) distH
        e3aR : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap2 Pair tj1 tj2))
                                   (ap1 Snd (ap1 Snd (ap2 Pair tj1 tj2)))))
        e3aR = axComp Snd Snd (ap2 Pair tj1 tj2)
        e3bR : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tj1 tj2)) tj2))
        e3bR = axSnd tj1 tj2
        e3cR : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair tj1 tj2)))
                                   (ap1 Snd tj2)))
        e3cR = cong1 Snd e3bR
        e3R : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap2 Pair tj1 tj2))
                                  (ap1 Snd tj2)))
        e3R = ruleTrans e3aR e3cR
        e4aR : Deriv (atomic (eqn (ap1 Snd tj2)
                                   (ap1 Snd (reify (codeFormula (atomic (eqn u v)))))))
        e4aR = cong1 Snd d2
        e4bR : Deriv (atomic (eqn (ap1 Snd (reify (codeFormula (atomic (eqn u v)))))
                                   payV_r))
        e4bR = axSnd payU_r payV_r
        e4R : Deriv (atomic (eqn (ap1 Snd tj2) payV_r))
        e4R = ruleTrans e4aR e4bR
        eR : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair) a bb)
          payV_r))
        eR = ruleTrans e1R (ruleTrans e2R (ruleTrans e3R e4R))
    in pairOfFan_eval (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair)
                      (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                      a bb payT_r payV_r eL eR

  thmTDispRuleTrans : (t u v : Term) (y1 y2 : Tree) (y1' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y1)) (ap2 Pair O y1'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y1))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y2))
                       (reify (codeFormula (atomic (eqn u v)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encRuleTrans y1 y2)))
                       (reify (outRuleTrans t v))))
  thmTDispRuleTrans t u v y1 y2 y1' shape d1 d2 =
    let payT = reify (nd y1 y2)
        a    = ap2 Pair tagCode_ruleTrans payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleTrans) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleSym payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleTrans payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleTrans refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleTrans payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleTrans refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleTrans payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleTrans refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleTrans payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleTrans refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleTrans payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleTrans refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleTrans payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleTrans refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleTrans payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleTrans refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleTrans payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleTrans refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleTrans payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleTrans refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleTrans payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagRuleTrans refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleTrans payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleTrans refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleTrans payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleTrans refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleTrans payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleTrans refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleTrans payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleTrans refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleTrans payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleTrans refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleTrans payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleTrans refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleTrans payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleTrans refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleTrans payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleTrans refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleTrans payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleTrans refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleTrans payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleTrans refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleTrans payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleTrans refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleTrans payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleTrans refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleTrans payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleTrans refl)
        hh   = hitAtTag  (natCode tagRuleTrans)   tagCode_ruleTrans payT b body_ruleTrans   next_ruleTrans
                  (teqEq tagRuleTrans)
        sndB_unfold : Deriv (atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleTrans) (ap1 thmT payT)
        distrib : Deriv (atomic (eqn (ap1 thmT payT)
                                      (ap2 Pair (ap1 thmT (reify y1))
                                                (ap1 thmT (reify y2)))))
        distrib = thmTDistrib y1 y2 y1' shape
        distH : Deriv (atomic (eqn (ap1 Snd b)
                                    (ap2 Pair (ap1 thmT (reify y1))
                                              (ap1 thmT (reify y2)))))
        distH = ruleTrans sndB_unfold distrib
        be = body_ruleTrans_eval t u v y1 y2 b distH d1 d2
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans hh be))))))))))))))))))))))))

  -- Parametric variant of body_ruleTrans_eval (Theorem 12 recursive cases).
  body_ruleTrans_eval_param : (y1T y2T bb : Term) (u1 u2 u3 u4 : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
    Deriv (atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4))) ->
    Deriv (atomic (eqn
      (ap2 body_ruleTrans (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)) bb)
      (ap2 Pair u1 u4)))
  body_ruleTrans_eval_param y1T y2T bb u1 u2 u3 u4 distH d1 d2 =
    let tj1 = ap1 thmT y1T
        tj2 = ap1 thmT y2T
        a   = ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)
        e1L = postSndBody_eval (Comp Fst Fst) a bb
        e2L = cong1 (Comp Fst Fst) distH
        e3aL = axComp Fst Fst (ap2 Pair tj1 tj2)
        e3bL = axFst tj1 tj2
        e3cL = cong1 Fst e3bL
        e3L = ruleTrans e3aL e3cL
        e4aL = cong1 Fst d1
        e4bL = axFst u1 u2
        e4L = ruleTrans e4aL e4bL
        eL  = ruleTrans e1L (ruleTrans e2L (ruleTrans e3L e4L))
        e1R = postSndBody_eval (Comp Snd Snd) a bb
        e2R = cong1 (Comp Snd Snd) distH
        e3aR = axComp Snd Snd (ap2 Pair tj1 tj2)
        e3bR = axSnd tj1 tj2
        e3cR = cong1 Snd e3bR
        e3R = ruleTrans e3aR e3cR
        e4aR = cong1 Snd d2
        e4bR = axSnd u3 u4
        e4R = ruleTrans e4aR e4bR
        eR  = ruleTrans e1R (ruleTrans e2R (ruleTrans e3R e4R))
    in pairOfFan_eval
         (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair)
         (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
         a bb u1 u4 eL eR

  -- Lifted version of body_ruleTrans_eval_param.
  -- Takes BOTH d1 and d2 as P-implication-form Derivs.
  body_ruleTrans_eval_param_lifted : (y1T y2T bb : Term) (u1 u2 u3 u4 : Term) ->
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4))) ->
    Deriv (P imp atomic (eqn
      (ap2 body_ruleTrans (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)) bb)
      (ap2 Pair u1 u4)))
  body_ruleTrans_eval_param_lifted y1T y2T bb u1 u2 u3 u4 P distH lifted_d1 lifted_d2 =
    let tj1 = ap1 thmT y1T
        tj2 = ap1 thmT y2T
        a   = ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)
        e1L = postSndBody_eval (Comp Fst Fst) a bb
        e2L = cong1 (Comp Fst Fst) distH
        e3aL = axComp Fst Fst (ap2 Pair tj1 tj2)
        e3bL = axFst tj1 tj2
        e3cL = cong1 Fst e3bL
        e3L = ruleTrans e3aL e3cL
        -- e4L uses d1: cong1 Fst d1 then ruleTrans with axFst u1 u2.
        lifted_e4aL = liftedCong1 P Fst tj1 (ap2 Pair u1 u2) lifted_d1
        lifted_e4bL = liftAxiom P (axFst u1 u2)
        lifted_e4L : Deriv (P imp atomic (eqn (ap1 Fst tj1) u1))
        lifted_e4L = liftedRuleTrans P (ap1 Fst tj1) (ap1 Fst (ap2 Pair u1 u2)) u1
                       lifted_e4aL lifted_e4bL
        -- eL = ruleTrans e1L (ruleTrans e2L (ruleTrans e3L e4L)).
        -- All except e4L are closed; e4L is lifted.
        e1L_e2L_e3L = ruleTrans e1L (ruleTrans e2L e3L)
        lifted_e1L_e2L_e3L = liftAxiom P e1L_e2L_e3L
        lifted_eL : Deriv (P imp atomic (eqn (ap2 (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair) a bb) u1))
        lifted_eL = liftedRuleTrans P
                      (ap2 (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair) a bb)
                      (ap1 Fst tj1)
                      u1
                      lifted_e1L_e2L_e3L lifted_e4L
        -- Right side similar.
        e1R = postSndBody_eval (Comp Snd Snd) a bb
        e2R = cong1 (Comp Snd Snd) distH
        e3aR = axComp Snd Snd (ap2 Pair tj1 tj2)
        e3bR = axSnd tj1 tj2
        e3cR = cong1 Snd e3bR
        e3R = ruleTrans e3aR e3cR
        lifted_e4aR = liftedCong1 P Snd tj2 (ap2 Pair u3 u4) lifted_d2
        lifted_e4bR = liftAxiom P (axSnd u3 u4)
        lifted_e4R : Deriv (P imp atomic (eqn (ap1 Snd tj2) u4))
        lifted_e4R = liftedRuleTrans P (ap1 Snd tj2) (ap1 Snd (ap2 Pair u3 u4)) u4
                       lifted_e4aR lifted_e4bR
        e1R_e2R_e3R = ruleTrans e1R (ruleTrans e2R e3R)
        lifted_e1R_e2R_e3R = liftAxiom P e1R_e2R_e3R
        lifted_eR : Deriv (P imp atomic (eqn (ap2 (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair) a bb) u4))
        lifted_eR = liftedRuleTrans P
                      (ap2 (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair) a bb)
                      (ap1 Snd tj2)
                      u4
                      lifted_e1R_e2R_e3R lifted_e4R
    in pairOfFan_eval_lifted P
         (Post (Comp (Comp Fst Fst) (Comp Snd Snd)) Pair)
         (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
         a bb u1 u4 lifted_eL lifted_eR

  -- Parametric variant of thmTDispRuleTrans.  Takes y1T, y2T : Term sub-encodings
  -- with their parametric thmT-images (Pair u1 u2 / Pair u3 u4) plus a head-shape
  -- proof on y1T (so thmTDistrib_param fires on the outer Pair).  Output is the
  -- ruleTrans-composed Pair u1 u4.
  thmTDispRuleTrans_param : (y1T y2T : Term) (u1 u2 u3 u4 : Term)
    (y1' : Term) (x' : Term) ->
    Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
      (ap2 Pair u1 u4)))
  thmTDispRuleTrans_param y1T y2T u1 u2 u3 u4 y1' x' shape d1 d2 =
    let payT = ap2 Pair y1T y2T
        a    = ap2 Pair tagCode_ruleTrans payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleTrans) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleSym payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleTrans payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleTrans refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleTrans payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleTrans refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleTrans payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleTrans refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleTrans payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleTrans refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleTrans payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleTrans refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleTrans payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleTrans refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleTrans payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleTrans refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleTrans payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleTrans refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleTrans payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleTrans refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleTrans payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagRuleTrans refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleTrans payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleTrans refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleTrans payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleTrans refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleTrans payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleTrans refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleTrans payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleTrans refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleTrans payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleTrans refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleTrans payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleTrans refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleTrans payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleTrans refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleTrans payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleTrans refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleTrans payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleTrans refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleTrans payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleTrans refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleTrans payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleTrans refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleTrans payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleTrans refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleTrans payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleTrans refl)
        hh   = hitAtTag  (natCode tagRuleTrans)   tagCode_ruleTrans payT b body_ruleTrans   next_ruleTrans
                  (teqEq tagRuleTrans)
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleTrans) (ap1 thmT payT)
        distrib = thmTDistrib_param y1T y2T y1' shape
        distH   = ruleTrans sndB_unfold distrib
        be      = body_ruleTrans_eval_param y1T y2T b u1 u2 u3 u4 distH d1 d2
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans hh be))))))))))))))))))))))))

  -- Lifted version of thmTDispRuleTrans_param.
  thmTDispRuleTrans_param_lifted : (y1T y2T : Term) (u1 u2 u3 u4 : Term)
    (y1' : Term) (x' : Term)
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4))) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
      (ap2 Pair u1 u4)))
  thmTDispRuleTrans_param_lifted y1T y2T u1 u2 u3 u4 y1' x' P shape lifted_d1 lifted_d2 =
    let payT = ap2 Pair y1T y2T
        a    = ap2 Pair tagCode_ruleTrans payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleTrans) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleSym payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleTrans payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleTrans refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleTrans payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleTrans refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleTrans payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleTrans refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleTrans payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleTrans refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleTrans payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleTrans refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleTrans payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleTrans refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleTrans payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleTrans refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleTrans payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleTrans refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleTrans payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleTrans refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleTrans payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagRuleTrans refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleTrans payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleTrans refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleTrans payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleTrans refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleTrans payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleTrans refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleTrans payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleTrans refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleTrans payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleTrans refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleTrans payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleTrans refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleTrans payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleTrans refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleTrans payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleTrans refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleTrans payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleTrans refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleTrans payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleTrans refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleTrans payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleTrans refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleTrans payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleTrans refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleTrans payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleTrans refl)
        hh   = hitAtTag  (natCode tagRuleTrans)   tagCode_ruleTrans payT b body_ruleTrans   next_ruleTrans
                  (teqEq tagRuleTrans)
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleTrans) (ap1 thmT payT)
        distrib = thmTDistrib_param y1T y2T y1' shape
        distH   = ruleTrans sndB_unfold distrib
        lifted_be = body_ruleTrans_eval_param_lifted y1T y2T b u1 u2 u3 u4 P distH
                      lifted_d1 lifted_d2
        chain_lifted = liftedRuleTrans P _ _ _ (liftAxiom P e1)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s1)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s2)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s3)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s4)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s5)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s6)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s7)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s8)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s9)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s10)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s11)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s12)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s13)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s14)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s15)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s16)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s17)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s18)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s19)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s20)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s21)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s22)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s23)
                       (liftedRuleTrans P _ _ _ (liftAxiom P hh)
                                              lifted_be))))))))))))))))))))))))
    in chain_lifted

  ------------------------------------------------------------------
  -- Head-shape lemmas for  codeF1 / codeF2  trees, used by cong1 /
  -- congL / congR / ruleInst dispatch chains.  Every codeF1 f starts
  -- with  nd (natCode N) ...  for some  N >= 26 ;  reify  of that is
  -- Pair O (reify (natCode (N-1))) , so axFst suffices.

  fstReifyCodeF1 : (f : Fun1) ->
    Sigma Term (\ y' ->
      Deriv (atomic (eqn (ap1 Fst (reify (codeF1 f))) (ap2 Pair O y'))))
  fstReifyCodeF1 I             = mkSigma _ (axFst _ _)
  fstReifyCodeF1 Fst           = mkSigma _ (axFst _ _)
  fstReifyCodeF1 Snd           = mkSigma _ (axFst _ _)
  fstReifyCodeF1 (Comp f g)    = mkSigma _ (axFst _ _)
  fstReifyCodeF1 (Comp2 h f g) = mkSigma _ (axFst _ _)
  fstReifyCodeF1 (Rec z s)     = mkSigma _ (axFst _ _)
  fstReifyCodeF1 Z             = mkSigma _ (axFst _ _)

  -- Same head-shape lemma for codeF2 (8 Fun2 constructors).
  fstReifyCodeF2 : (g : Fun2) ->
    Sigma Term (\ y' ->
      Deriv (atomic (eqn (ap1 Fst (reify (codeF2 g))) (ap2 Pair O y'))))
  fstReifyCodeF2 Pair          = mkSigma _ (axFst _ _)
  fstReifyCodeF2 Const         = mkSigma _ (axFst _ _)
  fstReifyCodeF2 (Lift f)      = mkSigma _ (axFst _ _)
  fstReifyCodeF2 (Post f h)    = mkSigma _ (axFst _ _)
  fstReifyCodeF2 (Fan h1 h2 h) = mkSigma _ (axFst _ _)
  fstReifyCodeF2 IfLf          = mkSigma _ (axFst _ _)
  fstReifyCodeF2 TreeEq        = mkSigma _ (axFst _ _)
  fstReifyCodeF2 (RecP s)      = mkSigma _ (axFst _ _)

  -- Head-shape lemma for  code (var x) : the variable encoding always
  -- starts with  nd tagVar (...)  where  tagVar = nd (nd (nd lf lf) lf) lf
  -- (a non-leaf), so reify of it is  Pair X O  with X non-trivial.
  -- Returns both  x' (the X)  and  y' (= O) , so ruleInst's dispatch
  -- can invoke the generalised  thmTDistrib .
  fstReifyCodeVar : (x : Nat) ->
    Sigma Term (\ x' -> Sigma Term (\ y' ->
      Deriv (atomic (eqn (ap1 Fst (reify (code (var x)))) (ap2 Pair x' y')))))
  fstReifyCodeVar x = mkSigma _ (mkSigma _ (axFst _ _))

  ------------------------------------------------------------------
  -- cong1 f y_h : RECURSIVE (1 sub-proof, payF in payload).  IH on
  -- y_h gives  thmT (reify y_h) = Pair payT_r payU_r ; the body
  -- assembles the cong1-conclusion code from payF (read from a) plus
  -- payT_r , payU_r (read from b after distribution).

  body_cong1_eval : (f : Fun1) (t u : Term) (y_h : Tree) (bb : Term) ->
    -- distH: Snd bb = Pair (thmT (reify (codeF1 f))) (thmT (reify y_h))
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF1 f)))
                                 (ap1 thmT (reify y_h))))) ->
    -- IH d_h: thmT (reify y_h) = reify (codeFormula (atomic (eqn t u)))
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn
      (ap2 body_cong1
            (ap2 Pair tagCode_cong1 (reify (nd (codeF1 f) y_h)))
            bb)
      (reify (outCong1 f t u))))
  body_cong1_eval f t u y_h bb distH d_h =
    let payF : Term
        payF = reify (codeF1 f)
        y_h_r : Term
        y_h_r = reify y_h
        tjF : Term
        tjF = ap1 thmT payF
        tjH : Term
        tjH = ap1 thmT y_h_r
        a : Term
        a = ap2 Pair tagCode_cong1 (ap2 Pair payF y_h_r)
        K_a1V : Tree
        K_a1V = tagAp1
        K_a1 : Term
        K_a1 = reify K_a1V
        payT_r : Term
        payT_r = reify (code t)
        payU_r : Term
        payU_r = reify (code u)
        -- payF extraction from a (no distH involvement).
        eF : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payF))
        eF = liftCompFstSnd_evalPair tagCode_cong1 payF y_h_r bb
        -- payT_r extraction: postSndBody_eval (Comp Fst Snd) gives
        --   ap1 (Comp Fst Snd) (ap1 Snd bb) = Fst(Snd(Snd bb)) ,
        -- then chain through distH and d_h.
        post_T : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp Fst Snd) (ap1 Snd bb))))
        post_T = postSndBody_eval (Comp Fst Snd) a bb
        post_T_distH : Deriv (atomic (eqn (ap1 (Comp Fst Snd) (ap1 Snd bb))
                                           (ap1 (Comp Fst Snd) (ap2 Pair tjF tjH))))
        post_T_distH = cong1 (Comp Fst Snd) distH
        compFS_pair : Deriv (atomic (eqn (ap1 (Comp Fst Snd) (ap2 Pair tjF tjH))
                                          (ap1 Fst (ap1 Snd (ap2 Pair tjF tjH)))))
        compFS_pair = axComp Fst Snd (ap2 Pair tjF tjH)
        snd_pair_T : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair_T = axSnd tjF tjH
        fst_snd_pair_T : Deriv (atomic (eqn (ap1 Fst (ap1 Snd (ap2 Pair tjF tjH)))
                                             (ap1 Fst tjH)))
        fst_snd_pair_T = cong1 Fst snd_pair_T
        compFS_to_FstTjH : Deriv (atomic (eqn
          (ap1 (Comp Fst Snd) (ap2 Pair tjF tjH))
          (ap1 Fst tjH)))
        compFS_to_FstTjH = ruleTrans compFS_pair fst_snd_pair_T
        fst_tjH : Deriv (atomic (eqn (ap1 Fst tjH)
                                      (ap1 Fst (reify (codeFormula
                                                       (atomic (eqn t u)))))))
        fst_tjH = cong1 Fst d_h
        fst_codeFormula_tu : Deriv (atomic (eqn
          (ap1 Fst (reify (codeFormula (atomic (eqn t u))))) payT_r))
        fst_codeFormula_tu = axFst payT_r payU_r
        fst_tjH_eq : Deriv (atomic (eqn (ap1 Fst tjH) payT_r))
        fst_tjH_eq = ruleTrans fst_tjH fst_codeFormula_tu
        eT : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb)
          payT_r))
        eT = ruleTrans post_T (ruleTrans post_T_distH
              (ruleTrans compFS_to_FstTjH fst_tjH_eq))
        -- payU_r extraction: postSndBody_eval (Comp Snd Snd) gives
        --   ap1 (Comp Snd Snd) (ap1 Snd bb) = Snd(Snd(Snd bb)) ,
        -- then chain through distH and d_h.
        post_U : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp Snd Snd) (ap1 Snd bb))))
        post_U = postSndBody_eval (Comp Snd Snd) a bb
        post_U_distH : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap1 Snd bb))
                                           (ap1 (Comp Snd Snd) (ap2 Pair tjF tjH))))
        post_U_distH = cong1 (Comp Snd Snd) distH
        compSS_pair : Deriv (atomic (eqn (ap1 (Comp Snd Snd) (ap2 Pair tjF tjH))
                                          (ap1 Snd (ap1 Snd (ap2 Pair tjF tjH)))))
        compSS_pair = axComp Snd Snd (ap2 Pair tjF tjH)
        snd_snd_pair_U : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair tjF tjH)))
                                             (ap1 Snd tjH)))
        snd_snd_pair_U = cong1 Snd snd_pair_T
        compSS_to_SndTjH : Deriv (atomic (eqn
          (ap1 (Comp Snd Snd) (ap2 Pair tjF tjH))
          (ap1 Snd tjH)))
        compSS_to_SndTjH = ruleTrans compSS_pair snd_snd_pair_U
        snd_tjH : Deriv (atomic (eqn (ap1 Snd tjH)
                                      (ap1 Snd (reify (codeFormula
                                                       (atomic (eqn t u)))))))
        snd_tjH = cong1 Snd d_h
        snd_codeFormula_tu : Deriv (atomic (eqn
          (ap1 Snd (reify (codeFormula (atomic (eqn t u))))) payU_r))
        snd_codeFormula_tu = axSnd payT_r payU_r
        snd_tjH_eq : Deriv (atomic (eqn (ap1 Snd tjH) payU_r))
        snd_tjH_eq = ruleTrans snd_tjH snd_codeFormula_tu
        eU : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair) a bb)
          payU_r))
        eU = ruleTrans post_U (ruleTrans post_U_distH
              (ruleTrans compSS_to_SndTjH snd_tjH_eq))
        -- Inner Pair (payF , payT_r) and (payF , payU_r).
        inner_LHS : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                    Pair) a bb)
          (ap2 Pair payF payT_r)))
        inner_LHS = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                       a bb payF payT_r eF eT
        inner_RHS : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                    Pair) a bb)
          (ap2 Pair payF payU_r)))
        inner_RHS = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                       a bb payF payU_r eF eU
        -- LHS-part: Pair K_a1 (Pair payF payT_r).
        outer_LHS : Deriv (atomic (eqn
          (ap2 (Fan (Lift (KT K_a1))
                    (Fan (Lift (Comp Fst Snd))
                         (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair K_a1 (ap2 Pair payF payT_r))))
        outer_LHS = pairOfConst_eval K_a1V
                       (Fan (Lift (Comp Fst Snd))
                            (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb (ap2 Pair payF payT_r) inner_LHS
        outer_RHS : Deriv (atomic (eqn
          (ap2 (Fan (Lift (KT K_a1))
                    (Fan (Lift (Comp Fst Snd))
                         (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair K_a1 (ap2 Pair payF payU_r))))
        outer_RHS = pairOfConst_eval K_a1V
                       (Fan (Lift (Comp Fst Snd))
                            (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb (ap2 Pair payF payU_r) inner_RHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a1 (ap2 Pair payF payT_r))
         (ap2 Pair K_a1 (ap2 Pair payF payU_r))
         outer_LHS outer_RHS

  thmTDispCong1 : (f : Fun1) (t u : Term) (y_h : Tree) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encCong1 f y_h)))
                       (reify (outCong1 f t u))))
  thmTDispCong1 f t u y_h d_h =
    let payT = reify (nd (codeF1 f) y_h)
        a    = ap2 Pair tagCode_cong1 payT
        b    = ap2 Pair (ap1 thmT tagCode_cong1) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleTrans payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_cong1 payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCong1 refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_cong1 payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCong1 refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_cong1 payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCong1 refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_cong1 payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCong1 refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_cong1 payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCong1 refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_cong1 payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCong1 refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_cong1 payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCong1 refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_cong1 payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCong1 refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_cong1 payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCong1 refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_cong1 payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagCong1 refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_cong1 payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCong1 refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_cong1 payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCong1 refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_cong1 payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCong1 refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_cong1 payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCong1 refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_cong1 payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCong1 refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_cong1 payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCong1 refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_cong1 payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCong1 refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_cong1 payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCong1 refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_cong1 payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCong1 refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_cong1 payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCong1 refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_cong1 payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCong1 refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_cong1 payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCong1 refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_cong1 payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCong1 refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_cong1 payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCong1 refl)
        hh   = hitAtTag  (natCode tagCong1)       tagCode_cong1 payT b body_cong1       next_cong1
                  (teqEq tagCong1)
        sndB_unfold : Deriv (atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndB_unfold = axSnd (ap1 thmT tagCode_cong1) (ap1 thmT payT)
        shapeF : Sigma Term (\ y' ->
          Deriv (atomic (eqn (ap1 Fst (reify (codeF1 f))) (ap2 Pair O y'))))
        shapeF = fstReifyCodeF1 f
        distrib : Deriv (atomic (eqn (ap1 thmT payT)
                                      (ap2 Pair (ap1 thmT (reify (codeF1 f)))
                                                (ap1 thmT (reify y_h)))))
        distrib = thmTDistrib (codeF1 f) y_h (fst shapeF) (snd shapeF)
        distH : Deriv (atomic (eqn (ap1 Snd b)
                                    (ap2 Pair (ap1 thmT (reify (codeF1 f)))
                                              (ap1 thmT (reify y_h)))))
        distH = ruleTrans sndB_unfold distrib
        be = body_cong1_eval f t u y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans hh be)))))))))))))))))))))))))

  -- Parametric variant of body_cong1_eval (Theorem 12 recursive cases).
  -- Takes parametric  y_h_T : Term  whose thmT-image is  Pair u1 u2 ;
  -- output wraps both halves in tagAp1 + codeF1 f.
  body_cong1_eval_param : (f : Fun1) (y_h_T : Term) (u1 u2 bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF1 f)))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap2 body_cong1
            (ap2 Pair tagCode_cong1
                  (ap2 Pair (reify (codeF1 f)) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) u1))
                (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) u2)))))
  body_cong1_eval_param f y_h_T u1 u2 bb distH d_h =
    let payF  = reify (codeF1 f)
        tjF   = ap1 thmT payF
        tjH   = ap1 thmT y_h_T
        a     = ap2 Pair tagCode_cong1 (ap2 Pair payF y_h_T)
        K_a1V = tagAp1
        K_a1  = reify K_a1V
        eF    = liftCompFstSnd_evalPair tagCode_cong1 payF y_h_T bb
        post_T = postSndBody_eval (Comp Fst Snd) a bb
        post_T_distH = cong1 (Comp Fst Snd) distH
        compFS_pair = axComp Fst Snd (ap2 Pair tjF tjH)
        snd_pair_T = axSnd tjF tjH
        fst_snd_pair_T = cong1 Fst snd_pair_T
        compFS_to_FstTjH = ruleTrans compFS_pair fst_snd_pair_T
        fst_tjH = cong1 Fst d_h
        fst_codeFormula_tu = axFst u1 u2
        fst_tjH_eq = ruleTrans fst_tjH fst_codeFormula_tu
        eT = ruleTrans post_T (ruleTrans post_T_distH
              (ruleTrans compFS_to_FstTjH fst_tjH_eq))
        post_U = postSndBody_eval (Comp Snd Snd) a bb
        post_U_distH = cong1 (Comp Snd Snd) distH
        compSS_pair = axComp Snd Snd (ap2 Pair tjF tjH)
        snd_snd_pair_U = cong1 Snd snd_pair_T
        compSS_to_SndTjH = ruleTrans compSS_pair snd_snd_pair_U
        snd_tjH = cong1 Snd d_h
        snd_codeFormula_tu = axSnd u1 u2
        snd_tjH_eq = ruleTrans snd_tjH snd_codeFormula_tu
        eU = ruleTrans post_U (ruleTrans post_U_distH
              (ruleTrans compSS_to_SndTjH snd_tjH_eq))
        inner_LHS = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                       a bb payF u1 eF eT
        inner_RHS = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                       a bb payF u2 eF eU
        outer_LHS = pairOfConst_eval K_a1V
                       (Fan (Lift (Comp Fst Snd))
                            (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb (ap2 Pair payF u1) inner_LHS
        outer_RHS = pairOfConst_eval K_a1V
                       (Fan (Lift (Comp Fst Snd))
                            (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb (ap2 Pair payF u2) inner_RHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a1))
              (Fan (Lift (Comp Fst Snd))
                   (Post (Comp (Comp Snd Snd) (Comp Snd Snd)) Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a1 (ap2 Pair payF u1))
         (ap2 Pair K_a1 (ap2 Pair payF u2))
         outer_LHS outer_RHS

  -- Parametric variant of thmTDispCong1.
  thmTDispCong1_param : (f : Fun1) (y_h_T : Term) (u1 u2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_cong1
                          (ap2 Pair (reify (codeF1 f)) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) u1))
                (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 f)) u2)))))
  thmTDispCong1_param f y_h_T u1 u2 d_h =
    let payT = ap2 Pair (reify (codeF1 f)) y_h_T
        a    = ap2 Pair tagCode_cong1 payT
        b    = ap2 Pair (ap1 thmT tagCode_cong1) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleTrans payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_cong1 payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCong1 refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_cong1 payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCong1 refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_cong1 payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCong1 refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_cong1 payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCong1 refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_cong1 payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCong1 refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_cong1 payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCong1 refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_cong1 payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCong1 refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_cong1 payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCong1 refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_cong1 payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCong1 refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_cong1 payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagCong1 refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_cong1 payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCong1 refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_cong1 payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCong1 refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_cong1 payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCong1 refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_cong1 payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCong1 refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_cong1 payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCong1 refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_cong1 payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCong1 refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_cong1 payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCong1 refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_cong1 payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCong1 refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_cong1 payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCong1 refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_cong1 payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCong1 refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_cong1 payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCong1 refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_cong1 payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCong1 refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_cong1 payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCong1 refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_cong1 payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCong1 refl)
        hh   = hitAtTag  (natCode tagCong1)       tagCode_cong1 payT b body_cong1       next_cong1
                  (teqEq tagCong1)
        sndB_unfold = axSnd (ap1 thmT tagCode_cong1) (ap1 thmT payT)
        shapeF = fstReifyCodeF1 f
        distrib = thmTDistrib_param (reify (codeF1 f)) y_h_T (fst shapeF) (snd shapeF)
        distH   = ruleTrans sndB_unfold distrib
        be      = body_cong1_eval_param f y_h_T u1 u2 b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans hh be)))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Helper: extract  ap1 X (Snd bb) -> ap1 X tjH  via cong1 X distH
  -- followed by a 4-step axComp chain unfolding Comp Z (Comp Fst Snd)
  -- on  Pair tjG (Pair tjH tjX) .  Takes a Term  tag  so it can be
  -- reused for congL and congR (only the outer tag differs).

  congLR_extractTj :
    (X : Fun1) (tag : Term) (y_h : Tree) (bb : Term)
    (sec third : Term) (val : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT sec)
                                 (ap2 Pair (ap1 thmT (reify y_h))
                                           (ap1 thmT third))))) ->
    Deriv (atomic (eqn (ap1 X (ap1 thmT (reify y_h))) val)) ->
    Deriv (atomic (eqn
      (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair)
            (ap2 Pair tag (ap2 Pair sec (ap2 Pair (reify y_h) third)))
            bb)
      val))
  congLR_extractTj X tag y_h bb sec third val distH X_tjH_eq =
    let y_h_r : Term
        y_h_r = reify y_h
        tjG : Term
        tjG = ap1 thmT sec
        tjH : Term
        tjH = ap1 thmT y_h_r
        tjX : Term
        tjX = ap1 thmT third
        a : Term
        a = ap2 Pair tag (ap2 Pair sec (ap2 Pair y_h_r third))
        innerPair : Term
        innerPair = ap2 Pair tjH tjX
        outerPair : Term
        outerPair = ap2 Pair tjG innerPair
        e_post : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp X (Comp Fst Snd)) (ap1 Snd bb))))
        e_post = postSndBody_eval (Comp X (Comp Fst Snd)) a bb
        e_dist : Deriv (atomic (eqn (ap1 (Comp X (Comp Fst Snd)) (ap1 Snd bb))
                                     (ap1 (Comp X (Comp Fst Snd)) outerPair)))
        e_dist = cong1 (Comp X (Comp Fst Snd)) distH
        e_unfX : Deriv (atomic (eqn (ap1 (Comp X (Comp Fst Snd)) outerPair)
                                     (ap1 X (ap1 (Comp Fst Snd) outerPair))))
        e_unfX = axComp X (Comp Fst Snd) outerPair
        e_unfFS : Deriv (atomic (eqn (ap1 (Comp Fst Snd) outerPair)
                                      (ap1 Fst (ap1 Snd outerPair))))
        e_unfFS = axComp Fst Snd outerPair
        e_snd : Deriv (atomic (eqn (ap1 Snd outerPair) innerPair))
        e_snd = axSnd tjG innerPair
        e_fst_snd : Deriv (atomic (eqn (ap1 Fst (ap1 Snd outerPair))
                                        (ap1 Fst innerPair)))
        e_fst_snd = cong1 Fst e_snd
        e_compFS : Deriv (atomic (eqn (ap1 (Comp Fst Snd) outerPair)
                                       (ap1 Fst innerPair)))
        e_compFS = ruleTrans e_unfFS e_fst_snd
        e_X_compFS : Deriv (atomic (eqn (ap1 X (ap1 (Comp Fst Snd) outerPair))
                                         (ap1 X (ap1 Fst innerPair))))
        e_X_compFS = cong1 X e_compFS
        e_unf_inner_fst : Deriv (atomic (eqn (ap1 Fst innerPair) tjH))
        e_unf_inner_fst = axFst tjH tjX
        e_X_inner : Deriv (atomic (eqn (ap1 X (ap1 Fst innerPair)) (ap1 X tjH)))
        e_X_inner = cong1 X e_unf_inner_fst
        e_X_outer : Deriv (atomic (eqn (ap1 (Comp X (Comp Fst Snd)) outerPair)
                                        (ap1 X tjH)))
        e_X_outer = ruleTrans e_unfX (ruleTrans e_X_compFS e_X_inner)
        e_chain : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          (ap1 X tjH)))
        e_chain = ruleTrans e_post (ruleTrans e_dist e_X_outer)
    in ruleTrans e_chain X_tjH_eq

  -- Parametric variant: y_h becomes y_h_T : Term.  Same proof, threaded
  -- over Term sub-witness.
  congLR_extractTj_param :
    (X : Fun1) (tag : Term) (y_h_T : Term) (bb : Term)
    (sec third : Term) (val : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT sec)
                                 (ap2 Pair (ap1 thmT y_h_T)
                                           (ap1 thmT third))))) ->
    Deriv (atomic (eqn (ap1 X (ap1 thmT y_h_T)) val)) ->
    Deriv (atomic (eqn
      (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair)
            (ap2 Pair tag (ap2 Pair sec (ap2 Pair y_h_T third)))
            bb)
      val))
  congLR_extractTj_param X tag y_h_T bb sec third val distH X_tjH_eq =
    let tjG = ap1 thmT sec
        tjH = ap1 thmT y_h_T
        tjX = ap1 thmT third
        a = ap2 Pair tag (ap2 Pair sec (ap2 Pair y_h_T third))
        innerPair = ap2 Pair tjH tjX
        outerPair = ap2 Pair tjG innerPair
        e_post = postSndBody_eval (Comp X (Comp Fst Snd)) a bb
        e_dist = cong1 (Comp X (Comp Fst Snd)) distH
        e_unfX = axComp X (Comp Fst Snd) outerPair
        e_unfFS = axComp Fst Snd outerPair
        e_snd = axSnd tjG innerPair
        e_fst_snd = cong1 Fst e_snd
        e_compFS = ruleTrans e_unfFS e_fst_snd
        e_X_compFS = cong1 X e_compFS
        e_unf_inner_fst = axFst tjH tjX
        e_X_inner = cong1 X e_unf_inner_fst
        e_X_outer = ruleTrans e_unfX (ruleTrans e_X_compFS e_X_inner)
        e_chain = ruleTrans e_post (ruleTrans e_dist e_X_outer)
    in ruleTrans e_chain X_tjH_eq

  -- Lifted version: distH and X_tjH_eq are taken as P-implication-form Derivs.
  congLR_extractTj_param_lifted :
    (P : Formula) (X : Fun1) (tag y_h_T bb sec third val : Term) ->
    Deriv (P imp atomic (eqn (ap1 Snd bb)
                              (ap2 Pair (ap1 thmT sec)
                                        (ap2 Pair (ap1 thmT y_h_T)
                                                  (ap1 thmT third))))) ->
    Deriv (P imp atomic (eqn (ap1 X (ap1 thmT y_h_T)) val)) ->
    Deriv (P imp atomic (eqn
      (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair)
            (ap2 Pair tag (ap2 Pair sec (ap2 Pair y_h_T third)))
            bb)
      val))
  congLR_extractTj_param_lifted P X tag y_h_T bb sec third val lifted_distH lifted_X_tjH_eq =
    let tjG = ap1 thmT sec
        tjH = ap1 thmT y_h_T
        tjX = ap1 thmT third
        a = ap2 Pair tag (ap2 Pair sec (ap2 Pair y_h_T third))
        innerPair = ap2 Pair tjH tjX
        outerPair = ap2 Pair tjG innerPair
        -- Closed sub-Derivs:
        e_post = postSndBody_eval (Comp X (Comp Fst Snd)) a bb
        e_unfX = axComp X (Comp Fst Snd) outerPair
        e_unfFS = axComp Fst Snd outerPair
        e_snd = axSnd tjG innerPair
        e_fst_snd = cong1 Fst e_snd
        e_compFS = ruleTrans e_unfFS e_fst_snd
        e_X_compFS = cong1 X e_compFS
        e_unf_inner_fst = axFst tjH tjX
        e_X_inner = cong1 X e_unf_inner_fst
        e_X_outer = ruleTrans e_unfX (ruleTrans e_X_compFS e_X_inner)
        -- Lifted version:
        lifted_e_post = liftAxiom P e_post
        lifted_e_dist : Deriv (P imp atomic (eqn (ap1 (Comp X (Comp Fst Snd)) (ap1 Snd bb))
                                                  (ap1 (Comp X (Comp Fst Snd)) outerPair)))
        lifted_e_dist = liftedCong1 P (Comp X (Comp Fst Snd)) (ap1 Snd bb) outerPair lifted_distH
        lifted_e_X_outer = liftAxiom P e_X_outer
        lifted_e_chain : Deriv (P imp atomic (eqn
          (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          (ap1 X tjH)))
        lifted_e_chain =
          liftedRuleTrans P
            (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
            (ap1 (Comp X (Comp Fst Snd)) (ap1 Snd bb))
            (ap1 X tjH)
            lifted_e_post
            (liftedRuleTrans P
              (ap1 (Comp X (Comp Fst Snd)) (ap1 Snd bb))
              (ap1 (Comp X (Comp Fst Snd)) outerPair)
              (ap1 X tjH)
              lifted_e_dist
              lifted_e_X_outer)
    in liftedRuleTrans P
         (ap2 (Post (Comp (Comp X (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
         (ap1 X tjH)
         val
         lifted_e_chain
         lifted_X_tjH_eq

  body_congL_eval : (g : Fun2) (x : Term) (t u : Term) (y_h : Tree)
                    (bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                                 (ap2 Pair (ap1 thmT (reify y_h))
                                           (ap1 thmT (reify (code x))))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (reify (nd (codeF2 g) (nd y_h (code x)))))
            bb)
      (reify (outCongL g x t u))))
  body_congL_eval g x t u y_h bb distH d_h =
    let payG : Term
        payG = reify (codeF2 g)
        y_h_r : Term
        y_h_r = reify y_h
        payX : Term
        payX = reify (code x)
        a : Term
        a = ap2 Pair tagCode_congL (ap2 Pair payG (ap2 Pair y_h_r payX))
        K_a2V : Tree
        K_a2V = tagAp2
        K_a2 : Term
        K_a2 = reify K_a2V
        payT_r : Term
        payT_r = reify (code t)
        payU_r : Term
        payU_r = reify (code u)
        eG : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payG))
        eG = liftCompFstSnd_evalPair tagCode_congL payG (ap2 Pair y_h_r payX) bb
        eX : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Snd Snd))) a bb) payX))
        eX = liftSndSndSnd_evalPair3 tagCode_congL payG y_h_r payX bb
        fst_tjH : Deriv (atomic (eqn (ap1 Fst (ap1 thmT y_h_r))
                                      (ap1 Fst (reify (codeFormula (atomic (eqn t u)))))))
        fst_tjH = cong1 Fst d_h
        fst_codeFormula_tu : Deriv (atomic (eqn
          (ap1 Fst (reify (codeFormula (atomic (eqn t u))))) payT_r))
        fst_codeFormula_tu = axFst payT_r payU_r
        fst_tjH_eq : Deriv (atomic (eqn (ap1 Fst (ap1 thmT y_h_r)) payT_r))
        fst_tjH_eq = ruleTrans fst_tjH fst_codeFormula_tu
        snd_tjH : Deriv (atomic (eqn (ap1 Snd (ap1 thmT y_h_r))
                                      (ap1 Snd (reify (codeFormula (atomic (eqn t u)))))))
        snd_tjH = cong1 Snd d_h
        snd_codeFormula_tu : Deriv (atomic (eqn
          (ap1 Snd (reify (codeFormula (atomic (eqn t u))))) payU_r))
        snd_codeFormula_tu = axSnd payT_r payU_r
        snd_tjH_eq : Deriv (atomic (eqn (ap1 Snd (ap1 thmT y_h_r)) payU_r))
        snd_tjH_eq = ruleTrans snd_tjH snd_codeFormula_tu
        eT : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          payT_r))
        eT = congLR_extractTj Fst tagCode_congL y_h bb payG payX payT_r
                              distH fst_tjH_eq
        eU : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          payU_r))
        eU = congLR_extractTj Snd tagCode_congL y_h bb payG payX payU_r
                              distH snd_tjH_eq
        innerL_pair : Deriv (atomic (eqn
          (ap2 (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                    (Lift (Comp Snd (Comp Snd Snd)))
                    Pair) a bb)
          (ap2 Pair payT_r payX)))
        innerL_pair = pairOfFan_eval
                       (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       (Lift (Comp Snd (Comp Snd Snd)))
                       a bb payT_r payX eT eX
        innerL : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                         (Lift (Comp Snd (Comp Snd Snd)))
                         Pair)
                    Pair) a bb)
          (ap2 Pair payG (ap2 Pair payT_r payX))))
        innerL = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       a bb payG (ap2 Pair payT_r payX) eG innerL_pair
        outerL : Deriv (atomic (eqn
          (ap2 (Fan (Lift (KT K_a2))
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                              (Lift (Comp Snd (Comp Snd Snd)))
                              Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payT_r payX)))))
        outerL = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 (Lift (Comp Snd (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair payT_r payX)) innerL
        innerR_pair : Deriv (atomic (eqn
          (ap2 (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                    (Lift (Comp Snd (Comp Snd Snd)))
                    Pair) a bb)
          (ap2 Pair payU_r payX)))
        innerR_pair = pairOfFan_eval
                       (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       (Lift (Comp Snd (Comp Snd Snd)))
                       a bb payU_r payX eU eX
        innerR : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                         (Lift (Comp Snd (Comp Snd Snd)))
                         Pair)
                    Pair) a bb)
          (ap2 Pair payG (ap2 Pair payU_r payX))))
        innerR = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       a bb payG (ap2 Pair payU_r payX) eG innerR_pair
        outerR : Deriv (atomic (eqn
          (ap2 (Fan (Lift (KT K_a2))
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                              (Lift (Comp Snd (Comp Snd Snd)))
                              Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payU_r payX)))))
        outerR = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 (Lift (Comp Snd (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair payU_r payX)) innerR
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payT_r payX)))
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payU_r payX)))
         outerL outerR

  thmTDispCongL : (g : Fun2) (x : Term) (t u : Term) (y_h : Tree)
                  (y_h' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encCongL g x y_h)))
                       (reify (outCongL g x t u))))
  thmTDispCongL g x t u y_h y_h' shape_h d_h =
    let payG : Term
        payG = reify (codeF2 g)
        y_h_r : Term
        y_h_r = reify y_h
        payX : Term
        payX = reify (code x)
        innerTree : Tree
        innerTree = nd y_h (code x)
        payT = reify (nd (codeF2 g) innerTree)
        a    = ap2 Pair tagCode_congL payT
        b    = ap2 Pair (ap1 thmT tagCode_congL) (ap1 thmT payT)
        e1   = dispatchOpens tagCong1 payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_congL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCongL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_congL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCongL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_congL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCongL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_congL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCongL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_congL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCongL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_congL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCongL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_congL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCongL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_congL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCongL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_congL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCongL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_congL payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagCongL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_congL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCongL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_congL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCongL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_congL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCongL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_congL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCongL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_congL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCongL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_congL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCongL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_congL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCongL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_congL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCongL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_congL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCongL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_congL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCongL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_congL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCongL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_congL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCongL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_congL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCongL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_congL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCongL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_congL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagCongL refl)
        hh   = hitAtTag  (natCode tagCongL)       tagCode_congL payT b body_congL       next_congL
                  (teqEq tagCongL)
        sndB_unfold : Deriv (atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndB_unfold = axSnd (ap1 thmT tagCode_congL) (ap1 thmT payT)
        shapeG : Sigma Term (\ y' ->
          Deriv (atomic (eqn (ap1 Fst (reify (codeF2 g))) (ap2 Pair O y'))))
        shapeG = fstReifyCodeF2 g
        distrib1 : Deriv (atomic (eqn (ap1 thmT payT)
          (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                     (ap1 thmT (reify innerTree)))))
        distrib1 = thmTDistrib (codeF2 g) innerTree (fst shapeG) (snd shapeG)
        distrib2 : Deriv (atomic (eqn (ap1 thmT (reify innerTree))
          (ap2 Pair (ap1 thmT (reify y_h))
                     (ap1 thmT (reify (code x))))))
        distrib2 = thmTDistrib y_h (code x) y_h' shape_h
        distrib2_lifted : Deriv (atomic (eqn
          (ap2 Pair (ap1 thmT (reify (codeF2 g))) (ap1 thmT (reify innerTree)))
          (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                     (ap2 Pair (ap1 thmT (reify y_h)) (ap1 thmT (reify (code x)))))))
        distrib2_lifted = congR Pair (ap1 thmT (reify (codeF2 g))) distrib2
        distrib : Deriv (atomic (eqn (ap1 thmT payT)
          (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                     (ap2 Pair (ap1 thmT (reify y_h)) (ap1 thmT (reify (code x)))))))
        distrib = ruleTrans distrib1 distrib2_lifted
        distH : Deriv (atomic (eqn (ap1 Snd b)
          (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                     (ap2 Pair (ap1 thmT (reify y_h)) (ap1 thmT (reify (code x)))))))
        distH = ruleTrans sndB_unfold distrib
        be = body_congL_eval g x t u y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans hh be))))))))))))))))))))))))))

  -- Parametric variant of body_congL_eval (Theorem 12 / Parts/Comp2.agda etc.).
  body_congL_eval_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                                 (ap2 Pair (ap1 thmT y_h_T)
                                           (ap1 thmT xT))))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  body_congL_eval_param g xT y_h_T u1 u2 bb distH d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congL (ap2 Pair payG (ap2 Pair y_h_T xT))
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        eG = liftCompFstSnd_evalPair tagCode_congL payG (ap2 Pair y_h_T xT) bb
        eX = liftSndSndSnd_evalPair3 tagCode_congL payG y_h_T xT bb
        fst_tjH = cong1 Fst d_h
        fst_pair = axFst u1 u2
        fst_tjH_eq = ruleTrans fst_tjH fst_pair
        snd_tjH = cong1 Snd d_h
        snd_pair = axSnd u1 u2
        snd_tjH_eq = ruleTrans snd_tjH snd_pair
        eT = congLR_extractTj_param Fst tagCode_congL y_h_T bb payG xT u1
                                     distH fst_tjH_eq
        eU = congLR_extractTj_param Snd tagCode_congL y_h_T bb payG xT u2
                                     distH snd_tjH_eq
        innerL_pair = pairOfFan_eval
                       (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       (Lift (Comp Snd (Comp Snd Snd)))
                       a bb u1 xT eT eX
        innerL = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       a bb payG (ap2 Pair u1 xT) eG innerL_pair
        outerL = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 (Lift (Comp Snd (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair u1 xT)) innerL
        innerR_pair = pairOfFan_eval
                       (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       (Lift (Comp Snd (Comp Snd Snd)))
                       a bb u2 xT eU eX
        innerR = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       a bb payG (ap2 Pair u2 xT) eG innerR_pair
        outerR = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 (Lift (Comp Snd (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair u2 xT)) innerR
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair u1 xT)))
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair u2 xT)))
         outerL outerR

  -- Lifted version of body_congL_eval_param.
  -- The d_h argument is now lifted (P imp eqn ...).
  -- distH stays a closed Deriv (callers pass it as-is — for our use it
  -- doesn't depend on d_h).
  body_congL_eval_param_lifted : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                                 (ap2 Pair (ap1 thmT y_h_T)
                                           (ap1 thmT xT))))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  body_congL_eval_param_lifted g xT y_h_T u1 u2 bb P distH lifted_d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congL (ap2 Pair payG (ap2 Pair y_h_T xT))
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        eG = liftCompFstSnd_evalPair tagCode_congL payG (ap2 Pair y_h_T xT) bb
        eX = liftSndSndSnd_evalPair3 tagCode_congL payG y_h_T xT bb
        lifted_eG = liftAxiom P eG
        lifted_eX = liftAxiom P eX
        lifted_distH = liftAxiom P distH

        -- fst_tjH_eq = ruleTrans (cong1 Fst d_h)(axFst u1 u2). Lifted:
        lifted_fst_tjH : Deriv (P imp atomic (eqn (ap1 Fst (ap1 thmT y_h_T))
                                                   (ap1 Fst (ap2 Pair u1 u2))))
        lifted_fst_tjH = liftedCong1 P Fst (ap1 thmT y_h_T) (ap2 Pair u1 u2) lifted_d_h
        lifted_fst_pair = liftAxiom P (axFst u1 u2)
        lifted_fst_tjH_eq : Deriv (P imp atomic (eqn (ap1 Fst (ap1 thmT y_h_T)) u1))
        lifted_fst_tjH_eq =
          liftedRuleTrans P
            (ap1 Fst (ap1 thmT y_h_T))
            (ap1 Fst (ap2 Pair u1 u2))
            u1
            lifted_fst_tjH lifted_fst_pair

        lifted_snd_tjH : Deriv (P imp atomic (eqn (ap1 Snd (ap1 thmT y_h_T))
                                                   (ap1 Snd (ap2 Pair u1 u2))))
        lifted_snd_tjH = liftedCong1 P Snd (ap1 thmT y_h_T) (ap2 Pair u1 u2) lifted_d_h
        lifted_snd_pair = liftAxiom P (axSnd u1 u2)
        lifted_snd_tjH_eq : Deriv (P imp atomic (eqn (ap1 Snd (ap1 thmT y_h_T)) u2))
        lifted_snd_tjH_eq =
          liftedRuleTrans P
            (ap1 Snd (ap1 thmT y_h_T))
            (ap1 Snd (ap2 Pair u1 u2))
            u2
            lifted_snd_tjH lifted_snd_pair

        lifted_eT = congLR_extractTj_param_lifted P Fst tagCode_congL y_h_T bb payG xT u1
                      lifted_distH lifted_fst_tjH_eq
        lifted_eU = congLR_extractTj_param_lifted P Snd tagCode_congL y_h_T bb payG xT u2
                      lifted_distH lifted_snd_tjH_eq

        lifted_innerL_pair = pairOfFan_eval_lifted P
                       (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       (Lift (Comp Snd (Comp Snd Snd)))
                       a bb u1 xT lifted_eT lifted_eX
        lifted_innerL = pairOfFan_eval_lifted P (Lift (Comp Fst Snd))
                       (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       a bb payG (ap2 Pair u1 xT) lifted_eG lifted_innerL_pair
        lifted_outerL = pairOfConst_eval_lifted P K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 (Lift (Comp Snd (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair u1 xT)) lifted_innerL

        lifted_innerR_pair = pairOfFan_eval_lifted P
                       (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       (Lift (Comp Snd (Comp Snd Snd)))
                       a bb u2 xT lifted_eU lifted_eX
        lifted_innerR = pairOfFan_eval_lifted P (Lift (Comp Fst Snd))
                       (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            (Lift (Comp Snd (Comp Snd Snd)))
                            Pair)
                       a bb payG (ap2 Pair u2 xT) lifted_eG lifted_innerR_pair
        lifted_outerR = pairOfConst_eval_lifted P K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 (Lift (Comp Snd (Comp Snd Snd)))
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair u2 xT)) lifted_innerR
    in pairOfFan_eval_lifted P
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        (Lift (Comp Snd (Comp Snd Snd)))
                        Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair u1 xT)))
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair u2 xT)))
         lifted_outerL lifted_outerR

  -- Parametric variant of thmTDispCongL.
  thmTDispCongL_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
                        (y_h' x' : Term) ->
    Deriv (atomic (eqn (ap1 Fst y_h_T) (ap2 Pair x' y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congL
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT))))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  thmTDispCongL_param g xT y_h_T u1 u2 y_h' x' shape_h d_h =
    let payT = ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)
        a    = ap2 Pair tagCode_congL payT
        b    = ap2 Pair (ap1 thmT tagCode_congL) (ap1 thmT payT)
        e1   = dispatchOpens tagCong1 payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_congL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCongL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_congL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCongL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_congL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCongL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_congL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCongL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_congL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCongL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_congL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCongL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_congL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCongL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_congL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCongL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_congL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCongL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_congL payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagCongL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_congL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCongL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_congL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCongL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_congL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCongL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_congL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCongL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_congL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCongL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_congL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCongL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_congL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCongL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_congL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCongL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_congL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCongL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_congL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCongL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_congL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCongL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_congL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCongL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_congL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCongL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_congL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCongL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_congL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagCongL refl)
        hh   = hitAtTag  (natCode tagCongL)       tagCode_congL payT b body_congL       next_congL
                  (teqEq tagCongL)
        sndB_unfold = axSnd (ap1 thmT tagCode_congL) (ap1 thmT payT)
        shapeG = fstReifyCodeF2 g
        innerT : Term
        innerT = ap2 Pair y_h_T xT
        distrib1 = thmTDistrib_param (reify (codeF2 g)) innerT (fst shapeG) (snd shapeG)
        distrib2 = thmTDistrib_param y_h_T xT y_h' shape_h
        distrib2_lifted = congR Pair (ap1 thmT (reify (codeF2 g))) distrib2
        distrib  = ruleTrans distrib1 distrib2_lifted
        distH    = ruleTrans sndB_unfold distrib
        be       = body_congL_eval_param g xT y_h_T u1 u2 b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans hh be))))))))))))))))))))))))))

  -- Lifted version of thmTDispCongL_param.
  -- All closed sub-Derivs (e1, s1..s25, hh, distH) are liftAxiom'd;
  -- be uses body_congL_eval_param_lifted with the lifted d_h.
  thmTDispCongL_param_lifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
    (y_h' x' : Term)
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Fst y_h_T) (ap2 Pair x' y_h'))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congL
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT))))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  thmTDispCongL_param_lifted g xT y_h_T u1 u2 y_h' x' P shape_h lifted_d_h =
    let payT = ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)
        a    = ap2 Pair tagCode_congL payT
        b    = ap2 Pair (ap1 thmT tagCode_congL) (ap1 thmT payT)
        e1   = dispatchOpens tagCong1 payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_congL payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCongL refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_congL payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCongL refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_congL payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCongL refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_congL payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCongL refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_congL payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCongL refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_congL payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCongL refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_congL payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCongL refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_congL payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCongL refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_congL payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCongL refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_congL payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagCongL refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_congL payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCongL refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_congL payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCongL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_congL payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCongL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_congL payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCongL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_congL payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCongL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_congL payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCongL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_congL payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCongL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_congL payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCongL refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_congL payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCongL refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_congL payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCongL refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_congL payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCongL refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_congL payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCongL refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_congL payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCongL refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_congL payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCongL refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_congL payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagCongL refl)
        hh   = hitAtTag  (natCode tagCongL)       tagCode_congL payT b body_congL       next_congL
                  (teqEq tagCongL)
        sndB_unfold = axSnd (ap1 thmT tagCode_congL) (ap1 thmT payT)
        shapeG = fstReifyCodeF2 g
        innerT : Term
        innerT = ap2 Pair y_h_T xT
        distrib1 = thmTDistrib_param (reify (codeF2 g)) innerT (fst shapeG) (snd shapeG)
        distrib2 = thmTDistrib_param y_h_T xT y_h' shape_h
        distrib2_lifted = congR Pair (ap1 thmT (reify (codeF2 g))) distrib2
        distrib  = ruleTrans distrib1 distrib2_lifted
        distH    = ruleTrans sndB_unfold distrib
        lifted_be = body_congL_eval_param_lifted g xT y_h_T u1 u2 b P distH lifted_d_h
        -- Compose all liftAxiom'd closed steps + lifted_be via liftedRuleTrans.
        chain_lifted = liftedRuleTrans P _ _ _ (liftAxiom P e1)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s1)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s2)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s3)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s4)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s5)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s6)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s7)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s8)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s9)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s10)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s11)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s12)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s13)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s14)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s15)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s16)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s17)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s18)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s19)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s20)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s21)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s22)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s23)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s24)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s25)
                       (liftedRuleTrans P _ _ _ (liftAxiom P hh)
                                              lifted_be))))))))))))))))))))))))))
    in chain_lifted

  ------------------------------------------------------------------
  -- congR g x y_h : same as congL but the inner pair has  payX
  -- BEFORE payT_r/payU_r .  Reuses  congL_extractTj  (which extracts
  --  ap1 X (thmT y_h_r)  for any  X ; symmetric wrt the inner pair).
  -- Note: the helper is named after congL but its proof works for
  -- any payload of the form  Pair payHead (Pair y_h_r payTail)  where
  -- payHead has the role of payG and payTail has the role of payX.
  -- For congR we still have payHead = payG = reify(codeF2 g) and
  -- payTail = payX = reify(code x), so the helper applies as-is.

  body_congR_eval : (g : Fun2) (x : Term) (t u : Term) (y_h : Tree)
                    (bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                                 (ap2 Pair (ap1 thmT (reify y_h))
                                           (ap1 thmT (reify (code x))))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (reify (nd (codeF2 g) (nd y_h (code x)))))
            bb)
      (reify (outCongR g x t u))))
  body_congR_eval g x t u y_h bb distH d_h =
    let payG : Term
        payG = reify (codeF2 g)
        y_h_r : Term
        y_h_r = reify y_h
        payX : Term
        payX = reify (code x)
        a : Term
        a = ap2 Pair tagCode_congR (ap2 Pair payG (ap2 Pair y_h_r payX))
        K_a2V : Tree
        K_a2V = tagAp2
        K_a2 : Term
        K_a2 = reify K_a2V
        payT_r : Term
        payT_r = reify (code t)
        payU_r : Term
        payU_r = reify (code u)
        eG : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payG))
        eG = liftCompFstSnd_evalPair tagCode_congR payG (ap2 Pair y_h_r payX) bb
        eX : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Snd Snd))) a bb) payX))
        eX = liftSndSndSnd_evalPair3 tagCode_congR payG y_h_r payX bb
        fst_tjH : Deriv (atomic (eqn (ap1 Fst (ap1 thmT y_h_r))
                                      (ap1 Fst (reify (codeFormula (atomic (eqn t u)))))))
        fst_tjH = cong1 Fst d_h
        fst_codeFormula_tu : Deriv (atomic (eqn
          (ap1 Fst (reify (codeFormula (atomic (eqn t u))))) payT_r))
        fst_codeFormula_tu = axFst payT_r payU_r
        fst_tjH_eq : Deriv (atomic (eqn (ap1 Fst (ap1 thmT y_h_r)) payT_r))
        fst_tjH_eq = ruleTrans fst_tjH fst_codeFormula_tu
        snd_tjH : Deriv (atomic (eqn (ap1 Snd (ap1 thmT y_h_r))
                                      (ap1 Snd (reify (codeFormula (atomic (eqn t u)))))))
        snd_tjH = cong1 Snd d_h
        snd_codeFormula_tu : Deriv (atomic (eqn
          (ap1 Snd (reify (codeFormula (atomic (eqn t u))))) payU_r))
        snd_codeFormula_tu = axSnd payT_r payU_r
        snd_tjH_eq : Deriv (atomic (eqn (ap1 Snd (ap1 thmT y_h_r)) payU_r))
        snd_tjH_eq = ruleTrans snd_tjH snd_codeFormula_tu
        eT : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          payT_r))
        eT = congLR_extractTj Fst tagCode_congR y_h bb payG payX payT_r
                              distH fst_tjH_eq
        eU : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair) a bb)
          payU_r))
        eU = congLR_extractTj Snd tagCode_congR y_h bb payG payX payU_r
                              distH snd_tjH_eq
        innerL_pair : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Snd (Comp Snd Snd)))
                    (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                    Pair) a bb)
          (ap2 Pair payX payT_r)))
        innerL_pair = pairOfFan_eval
                       (Lift (Comp Snd (Comp Snd Snd)))
                       (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       a bb payX payT_r eX eT
        innerL : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Fan (Lift (Comp Snd (Comp Snd Snd)))
                         (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair payG (ap2 Pair payX payT_r))))
        innerL = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Lift (Comp Snd (Comp Snd Snd)))
                            (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb payG (ap2 Pair payX payT_r) eG innerL_pair
        outerL : Deriv (atomic (eqn
          (ap2 (Fan (Lift (KT K_a2))
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Lift (Comp Snd (Comp Snd Snd)))
                              (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                              Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payX payT_r)))))
        outerL = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd Snd)))
                                 (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair payX payT_r)) innerL
        innerR_pair : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Snd (Comp Snd Snd)))
                    (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                    Pair) a bb)
          (ap2 Pair payX payU_r)))
        innerR_pair = pairOfFan_eval
                       (Lift (Comp Snd (Comp Snd Snd)))
                       (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       a bb payX payU_r eX eU
        innerR : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Fan (Lift (Comp Snd (Comp Snd Snd)))
                         (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair payG (ap2 Pair payX payU_r))))
        innerR = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Lift (Comp Snd (Comp Snd Snd)))
                            (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb payG (ap2 Pair payX payU_r) eG innerR_pair
        outerR : Deriv (atomic (eqn
          (ap2 (Fan (Lift (KT K_a2))
                    (Fan (Lift (Comp Fst Snd))
                         (Fan (Lift (Comp Snd (Comp Snd Snd)))
                              (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                              Pair)
                         Pair)
                    Pair) a bb)
          (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payX payU_r)))))
        outerR = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd Snd)))
                                 (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair payX payU_r)) innerR
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payX payT_r)))
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair payX payU_r)))
         outerL outerR

  thmTDispCongR : (g : Fun2) (x : Term) (t u : Term) (y_h : Tree)
                  (y_h' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encCongR g x y_h)))
                       (reify (outCongR g x t u))))
  thmTDispCongR g x t u y_h y_h' shape_h d_h =
    let innerTree : Tree
        innerTree = nd y_h (code x)
        payT = reify (nd (codeF2 g) innerTree)
        a    = ap2 Pair tagCode_congR payT
        b    = ap2 Pair (ap1 thmT tagCode_congR) (ap1 thmT payT)
        e1   = dispatchOpens tagCongL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_congR payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCongR refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_congR payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCongR refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_congR payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCongR refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_congR payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCongR refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_congR payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCongR refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_congR payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCongR refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_congR payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCongR refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_congR payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCongR refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_congR payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCongR refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_congR payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagCongR refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_congR payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCongR refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_congR payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCongR refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_congR payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCongR refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_congR payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCongR refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_congR payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCongR refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_congR payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCongR refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_congR payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCongR refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_congR payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCongR refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_congR payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCongR refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_congR payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCongR refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_congR payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCongR refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_congR payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCongR refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_congR payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCongR refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_congR payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCongR refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_congR payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagCongR refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_congR payT b body_congL       next_congL
                  (teqDiff tagCongL       tagCongR refl)
        hh   = hitAtTag  (natCode tagCongR)       tagCode_congR payT b body_congR       next_congR
                  (teqEq tagCongR)
        sndB_unfold : Deriv (atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndB_unfold = axSnd (ap1 thmT tagCode_congR) (ap1 thmT payT)
        shapeG = fstReifyCodeF2 g
        distrib1 = thmTDistrib (codeF2 g) innerTree (fst shapeG) (snd shapeG)
        distrib2 = thmTDistrib y_h (code x) y_h' shape_h
        distrib2_lifted = congR Pair (ap1 thmT (reify (codeF2 g))) distrib2
        distrib = ruleTrans distrib1 distrib2_lifted
        distH = ruleTrans sndB_unfold distrib
        be = body_congR_eval g x t u y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans hh be)))))))))))))))))))))))))))

  -- Parametric variant of body_congR_eval (Theorem 12 / Comp2/Fan etc.).
  body_congR_eval_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                                 (ap2 Pair (ap1 thmT y_h_T)
                                           (ap1 thmT xT))))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  body_congR_eval_param g xT y_h_T u1 u2 bb distH d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congR (ap2 Pair payG (ap2 Pair y_h_T xT))
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        eG = liftCompFstSnd_evalPair tagCode_congR payG (ap2 Pair y_h_T xT) bb
        eX = liftSndSndSnd_evalPair3 tagCode_congR payG y_h_T xT bb
        fst_tjH = cong1 Fst d_h
        fst_pair = axFst u1 u2
        fst_tjH_eq = ruleTrans fst_tjH fst_pair
        snd_tjH = cong1 Snd d_h
        snd_pair = axSnd u1 u2
        snd_tjH_eq = ruleTrans snd_tjH snd_pair
        eT = congLR_extractTj_param Fst tagCode_congR y_h_T bb payG xT u1
                                     distH fst_tjH_eq
        eU = congLR_extractTj_param Snd tagCode_congR y_h_T bb payG xT u2
                                     distH snd_tjH_eq
        innerL_pair = pairOfFan_eval
                       (Lift (Comp Snd (Comp Snd Snd)))
                       (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       a bb xT u1 eX eT
        innerL = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Lift (Comp Snd (Comp Snd Snd)))
                            (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb payG (ap2 Pair xT u1) eG innerL_pair
        outerL = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd Snd)))
                                 (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair xT u1)) innerL
        innerR_pair = pairOfFan_eval
                       (Lift (Comp Snd (Comp Snd Snd)))
                       (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       a bb xT u2 eX eU
        innerR = pairOfFan_eval (Lift (Comp Fst Snd))
                       (Fan (Lift (Comp Snd (Comp Snd Snd)))
                            (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb payG (ap2 Pair xT u2) eG innerR_pair
        outerR = pairOfConst_eval K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd Snd)))
                                 (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair xT u2)) innerR
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair xT u1)))
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair xT u2)))
         outerL outerR

  -- Lifted version of body_congR_eval_param.
  body_congR_eval_param_lifted : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (codeF2 g)))
                                 (ap2 Pair (ap1 thmT y_h_T)
                                           (ap1 thmT xT))))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  body_congR_eval_param_lifted g xT y_h_T u1 u2 bb P distH lifted_d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congR (ap2 Pair payG (ap2 Pair y_h_T xT))
        K_a2V = tagAp2
        K_a2  = reify K_a2V
        eG = liftCompFstSnd_evalPair tagCode_congR payG (ap2 Pair y_h_T xT) bb
        eX = liftSndSndSnd_evalPair3 tagCode_congR payG y_h_T xT bb
        lifted_eG = liftAxiom P eG
        lifted_eX = liftAxiom P eX
        lifted_distH = liftAxiom P distH

        lifted_fst_tjH = liftedCong1 P Fst (ap1 thmT y_h_T) (ap2 Pair u1 u2) lifted_d_h
        lifted_fst_pair = liftAxiom P (axFst u1 u2)
        lifted_fst_tjH_eq =
          liftedRuleTrans P
            (ap1 Fst (ap1 thmT y_h_T))
            (ap1 Fst (ap2 Pair u1 u2))
            u1
            lifted_fst_tjH lifted_fst_pair

        lifted_snd_tjH = liftedCong1 P Snd (ap1 thmT y_h_T) (ap2 Pair u1 u2) lifted_d_h
        lifted_snd_pair = liftAxiom P (axSnd u1 u2)
        lifted_snd_tjH_eq =
          liftedRuleTrans P
            (ap1 Snd (ap1 thmT y_h_T))
            (ap1 Snd (ap2 Pair u1 u2))
            u2
            lifted_snd_tjH lifted_snd_pair

        lifted_eT = congLR_extractTj_param_lifted P Fst tagCode_congR y_h_T bb payG xT u1
                      lifted_distH lifted_fst_tjH_eq
        lifted_eU = congLR_extractTj_param_lifted P Snd tagCode_congR y_h_T bb payG xT u2
                      lifted_distH lifted_snd_tjH_eq

        lifted_innerL_pair = pairOfFan_eval_lifted P
                       (Lift (Comp Snd (Comp Snd Snd)))
                       (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       a bb xT u1 lifted_eX lifted_eT
        lifted_innerL = pairOfFan_eval_lifted P (Lift (Comp Fst Snd))
                       (Fan (Lift (Comp Snd (Comp Snd Snd)))
                            (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb payG (ap2 Pair xT u1) lifted_eG lifted_innerL_pair
        lifted_outerL = pairOfConst_eval_lifted P K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd Snd)))
                                 (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair xT u1)) lifted_innerL

        lifted_innerR_pair = pairOfFan_eval_lifted P
                       (Lift (Comp Snd (Comp Snd Snd)))
                       (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                       a bb xT u2 lifted_eX lifted_eU
        lifted_innerR = pairOfFan_eval_lifted P (Lift (Comp Fst Snd))
                       (Fan (Lift (Comp Snd (Comp Snd Snd)))
                            (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                            Pair)
                       a bb payG (ap2 Pair xT u2) lifted_eG lifted_innerR_pair
        lifted_outerR = pairOfConst_eval_lifted P K_a2V
                       (Fan (Lift (Comp Fst Snd))
                            (Fan (Lift (Comp Snd (Comp Snd Snd)))
                                 (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                                 Pair)
                            Pair)
                       a bb (ap2 Pair payG (ap2 Pair xT u2)) lifted_innerR
    in pairOfFan_eval_lifted P
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Post (Comp (Comp Fst (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        Pair)
                   Pair)
              Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Lift (Comp Snd (Comp Snd Snd)))
                        (Post (Comp (Comp Snd (Comp Fst Snd)) (Comp Snd Snd)) Pair)
                        Pair)
                   Pair)
              Pair)
         a bb
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair xT u1)))
         (ap2 Pair K_a2 (ap2 Pair payG (ap2 Pair xT u2)))
         lifted_outerL lifted_outerR

  -- Parametric variant of thmTDispCongR.
  thmTDispCongR_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
                        (y_h' x' : Term) ->
    Deriv (atomic (eqn (ap1 Fst y_h_T) (ap2 Pair x' y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congR
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT))))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  thmTDispCongR_param g xT y_h_T u1 u2 y_h' x' shape_h d_h =
    let payT = ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)
        a    = ap2 Pair tagCode_congR payT
        b    = ap2 Pair (ap1 thmT tagCode_congR) (ap1 thmT payT)
        e1   = dispatchOpens tagCongL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_congR payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCongR refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_congR payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCongR refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_congR payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCongR refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_congR payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCongR refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_congR payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCongR refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_congR payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCongR refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_congR payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCongR refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_congR payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCongR refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_congR payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCongR refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_congR payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagCongR refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_congR payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCongR refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_congR payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCongR refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_congR payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCongR refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_congR payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCongR refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_congR payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCongR refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_congR payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCongR refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_congR payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCongR refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_congR payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCongR refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_congR payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCongR refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_congR payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCongR refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_congR payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCongR refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_congR payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCongR refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_congR payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCongR refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_congR payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCongR refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_congR payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagCongR refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_congR payT b body_congL       next_congL
                  (teqDiff tagCongL       tagCongR refl)
        hh   = hitAtTag  (natCode tagCongR)       tagCode_congR payT b body_congR       next_congR
                  (teqEq tagCongR)
        sndB_unfold = axSnd (ap1 thmT tagCode_congR) (ap1 thmT payT)
        shapeG = fstReifyCodeF2 g
        innerT : Term
        innerT = ap2 Pair y_h_T xT
        distrib1 = thmTDistrib_param (reify (codeF2 g)) innerT (fst shapeG) (snd shapeG)
        distrib2 = thmTDistrib_param y_h_T xT y_h' shape_h
        distrib2_lifted = congR Pair (ap1 thmT (reify (codeF2 g))) distrib2
        distrib  = ruleTrans distrib1 distrib2_lifted
        distH    = ruleTrans sndB_unfold distrib
        be       = body_congR_eval_param g xT y_h_T u1 u2 b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans hh be)))))))))))))))))))))))))))

  -- Lifted version of thmTDispCongR_param.
  thmTDispCongR_param_lifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
    (y_h' x' : Term)
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Fst y_h_T) (ap2 Pair x' y_h'))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congR
                  (ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT))))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  thmTDispCongR_param_lifted g xT y_h_T u1 u2 y_h' x' P shape_h lifted_d_h =
    let payT = ap2 Pair (reify (codeF2 g)) (ap2 Pair y_h_T xT)
        a    = ap2 Pair tagCode_congR payT
        b    = ap2 Pair (ap1 thmT tagCode_congR) (ap1 thmT payT)
        e1   = dispatchOpens tagCongL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_congR payT b body_axI         next_axI
                  (teqDiff tagAxI         tagCongR refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_congR payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagCongR refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_congR payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagCongR refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_congR payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagCongR refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_congR payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagCongR refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_congR payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagCongR refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_congR payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagCongR refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_congR payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagCongR refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_congR payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagCongR refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_congR payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagCongR refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_congR payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagCongR refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_congR payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagCongR refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_congR payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagCongR refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_congR payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagCongR refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_congR payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagCongR refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_congR payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagCongR refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_congR payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagCongR refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_congR payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagCongR refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_congR payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagCongR refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_congR payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagCongR refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_congR payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagCongR refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_congR payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagCongR refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_congR payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagCongR refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_congR payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagCongR refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_congR payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagCongR refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_congR payT b body_congL       next_congL
                  (teqDiff tagCongL       tagCongR refl)
        hh   = hitAtTag  (natCode tagCongR)       tagCode_congR payT b body_congR       next_congR
                  (teqEq tagCongR)
        sndB_unfold = axSnd (ap1 thmT tagCode_congR) (ap1 thmT payT)
        shapeG = fstReifyCodeF2 g
        innerT : Term
        innerT = ap2 Pair y_h_T xT
        distrib1 = thmTDistrib_param (reify (codeF2 g)) innerT (fst shapeG) (snd shapeG)
        distrib2 = thmTDistrib_param y_h_T xT y_h' shape_h
        distrib2_lifted = congR Pair (ap1 thmT (reify (codeF2 g))) distrib2
        distrib  = ruleTrans distrib1 distrib2_lifted
        distH    = ruleTrans sndB_unfold distrib
        lifted_be = body_congR_eval_param_lifted g xT y_h_T u1 u2 b P distH lifted_d_h
        chain_lifted = liftedRuleTrans P _ _ _ (liftAxiom P e1)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s1)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s2)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s3)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s4)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s5)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s6)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s7)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s8)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s9)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s10)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s11)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s12)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s13)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s14)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s15)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s16)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s17)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s18)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s19)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s20)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s21)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s22)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s23)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s24)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s25)
                       (liftedRuleTrans P _ _ _ (liftAxiom P s26)
                       (liftedRuleTrans P _ _ _ (liftAxiom P hh)
                                              lifted_be)))))))))))))))))))))))))))
    in chain_lifted

  ------------------------------------------------------------------
  -- ruleInst x t y_h : RECURSIVE (1 sub-proof + var index + term).
  -- Body uses subT  (BRA.SubT) to apply substitution at code level.
  --
  -- subTDef gives:
  --   ap2 subT (Pair (reify(code(var x))) (reify(code t))) (reify(codeFormula P))
  --     = reify(codedSubst (code t) (code (var x)) (codeFormula P))
  --
  -- codeCommutesFormula  (BRA.CodeCommutes) gives the Eq:
  --   codeFormula (substF x t P) = codedSubst (code t) (code (var x)) (codeFormula P)
  --
  -- Combined: subT(args, codeFormulaP) = reify(outRuleInst x t P).

  body_ruleInst_eval : (x : Nat) (t : Term) (P : Formula) (y_h : Tree) (bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (code (var x))))
                                 (ap2 Pair (ap1 thmT (reify y_h))
                                           (ap1 thmT (reify (code t))))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula P)))) ->
    Deriv (atomic (eqn
      (ap2 body_ruleInst
            (ap2 Pair tagCode_ruleInst
                  (reify (nd (code (var x)) (nd y_h (code t)))))
            bb)
      (reify (outRuleInst x t P))))
  body_ruleInst_eval x t P y_h bb distH d_h =
    let payVarX : Term
        payVarX = reify (code (var x))
        payT_T : Term
        payT_T = reify (code t)
        y_h_r : Term
        y_h_r = reify y_h
        tjV : Term
        tjV = ap1 thmT payVarX
        tjH : Term
        tjH = ap1 thmT y_h_r
        tjT : Term
        tjT = ap1 thmT payT_T
        a : Term
        a = ap2 Pair tagCode_ruleInst (ap2 Pair payVarX (ap2 Pair y_h_r payT_T))
        codeFP : Term
        codeFP = reify (codeFormula P)
        argsPair : Term
        argsPair = ap2 Pair payVarX payT_T
        eVarX : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payVarX))
        eVarX = liftCompFstSnd_evalPair tagCode_ruleInst payVarX
                  (ap2 Pair y_h_r payT_T) bb
        eT : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Snd Snd))) a bb) payT_T))
        eT = liftSndSndSnd_evalPair3 tagCode_ruleInst payVarX y_h_r payT_T bb
        eARGS : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Lift (Comp Snd (Comp Snd Snd)))
                    Pair) a bb)
          argsPair))
        eARGS = pairOfFan_eval (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd)))
                               a bb payVarX payT_T eVarX eT
        ePost = postSndBody_eval (Comp Fst Snd) a bb
        eDist = cong1 (Comp Fst Snd) distH
        outerPair : Term
        outerPair = ap2 Pair tjV (ap2 Pair tjH tjT)
        eUnfFS = axComp Fst Snd outerPair
        eSnd = axSnd tjV (ap2 Pair tjH tjT)
        eFstSnd = cong1 Fst eSnd
        eCompFS_to_FstInner = ruleTrans eUnfFS eFstSnd
        eInnerFst = axFst tjH tjT
        eCompFS_to_tjH = ruleTrans eCompFS_to_FstInner eInnerFst
        eCODEP_to_tjH : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb) tjH))
        eCODEP_to_tjH = ruleTrans ePost (ruleTrans eDist eCompFS_to_tjH)
        eCODEP : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb) codeFP))
        eCODEP = ruleTrans eCODEP_to_tjH d_h
        -- Apply axFan to body_ruleInst: ap2 body_ruleInst a bb =
        --   ap2 subT (ARGS_extractor a bb) (CODEP_extractor a bb).
        eFanBody : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
          (ap2 subT
            (ap2 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Snd (Comp Snd Snd)))
                      Pair) a bb)
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))))
        eFanBody = axFan (Fan (Lift (Comp Fst Snd))
                              (Lift (Comp Snd (Comp Snd Snd)))
                              Pair)
                         (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                         subT a bb
        -- Rewrite first subT arg to argsPair via eARGS.
        eL : Deriv (atomic (eqn
          (ap2 subT
            (ap2 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Snd (Comp Snd Snd)))
                      Pair) a bb)
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))
          (ap2 subT argsPair
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))))
        eL = congL subT (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb) eARGS
        -- Rewrite second subT arg to codeFP via eCODEP.
        eR : Deriv (atomic (eqn
          (ap2 subT argsPair
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))
          (ap2 subT argsPair codeFP)))
        eR = congR subT argsPair eCODEP
        -- Combined: ap2 body_ruleInst a bb = ap2 subT argsPair codeFP.
        eBody_to_subT : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
                                            (ap2 subT argsPair codeFP)))
        eBody_to_subT = ruleTrans eFanBody (ruleTrans eL eR)
        -- subTDef: subT(argsPair, codeFP) = reify(codedSubst (code t) (code (var x)) (codeFormula P)).
        eSubT : Deriv (atomic (eqn (ap2 subT argsPair codeFP)
                                    (reify (codedSubst (code t) (code (var x))
                                                       (codeFormula P)))))
        eSubT = subTDef x (code t) (codeFormula P)
        eBody_to_codedSubst : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
          (reify (codedSubst (code t) (code (var x)) (codeFormula P)))))
        eBody_to_codedSubst = ruleTrans eBody_to_subT eSubT
        -- Convert via codeCommutesFormula:
        --   codeFormula (substF x t P)  =  codedSubst (code t) (code (var x)) (codeFormula P)
        treeEq : Eq (codedSubst (code t) (code (var x)) (codeFormula P))
                    (codeFormula (substF x t P))
        treeEq = eqSym (codeCommutesFormula x t P)
    in eqSubst (\ T -> Deriv (atomic (eqn (ap2 body_ruleInst a bb) (reify T))))
               treeEq eBody_to_codedSubst

  thmTDispRuleInst : (x : Nat) (t : Term) (P : Formula) (y_h : Tree)
                     (y_h' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula P)))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst x t y_h)))
                       (reify (outRuleInst x t P))))
  thmTDispRuleInst x t P y_h y_h' shape_h d_h =
    let innerTree = nd y_h (code t)
        payT = reify (nd (code (var x)) innerTree)
        a    = ap2 Pair tagCode_ruleInst payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
        e1   = dispatchOpens tagMp payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleInst payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleInst refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleInst payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleInst refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleInst payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleInst refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleInst payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleInst refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleInst payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleInst refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleInst payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleInst refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleInst payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleInst refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleInst payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleInst refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleInst payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleInst refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleInst payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagRuleInst refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleInst payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleInst refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleInst payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleInst refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleInst payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleInst refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleInst payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleInst refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleInst payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleInst refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleInst payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleInst refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleInst payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleInst refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleInst payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleInst refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleInst payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleInst refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleInst payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleInst refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleInst payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleInst refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleInst payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleInst refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleInst payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleInst refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_ruleInst payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagRuleInst refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_ruleInst payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagRuleInst refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_ruleInst payT b body_congL       next_congL
                  (teqDiff tagCongL       tagRuleInst refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_ruleInst payT b body_congR       next_congR
                  (teqDiff tagCongR       tagRuleInst refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_ruleInst payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagRuleInst refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_ruleInst payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagRuleInst refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_ruleInst payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagRuleInst refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_ruleInst payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagRuleInst refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_ruleInst payT b body_axK         next_axK
                  (teqDiff tagAxK         tagRuleInst refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_ruleInst payT b body_axS         next_axS
                  (teqDiff tagAxS         tagRuleInst refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_ruleInst payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagRuleInst refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_ruleInst payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagRuleInst refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_ruleInst payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagRuleInst refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_ruleInst payT b body_mp          next_mp
                  (teqDiff tagMp          tagRuleInst refl)
        hh   = hitAtTag  (natCode tagRuleInst)    tagCode_ruleInst payT b body_ruleInst    next_ruleInst
                  (teqEq tagRuleInst)
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
        shapeV = fstReifyCodeVar x
        distrib1 = thmTDistrib (code (var x)) innerTree {x' = fst shapeV}
                               (fst (snd shapeV)) (snd (snd shapeV))
        distrib2 = thmTDistrib y_h (code t) y_h' shape_h
        distrib2_lifted = congR Pair (ap1 thmT (reify (code (var x)))) distrib2
        distrib = ruleTrans distrib1 distrib2_lifted
        distH = ruleTrans sndB_unfold distrib
        be = body_ruleInst_eval x t P y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Parametric variant of body_ruleInst_eval / thmTDispRuleInst.
  -- Takes the proof index as Term (xT) instead of Tree (y_h).
  --
  -- Used by step 4 of Theorem 14 (Goedel II's closure).  Caller
  -- supplies distHParam (parametric distribution of bb's Snd) and
  -- d_h (proof index's thmT-image).

  body_ruleInst_eval_param :
    (n : Nat) (tT xT : Term) (bb : Term)
    (codeP : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (reify (code (var n))))
                                 (ap2 Pair (ap1 thmT xT) (ap1 thmT tT))))) ->
    Deriv (atomic (eqn (ap1 thmT xT) codeP)) ->
    Deriv (atomic (eqn
      (ap2 body_ruleInst
            (ap2 Pair tagCode_ruleInst
                  (ap2 Pair (reify (code (var n))) (ap2 Pair xT tT)))
            bb)
      (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
  body_ruleInst_eval_param n tT xT bb codeP distH d_h =
    let payVarX : Term
        payVarX = reify (code (var n))
        payT_T : Term
        payT_T = tT
        y_h_r : Term
        y_h_r = xT
        tjV : Term
        tjV = ap1 thmT payVarX
        tjH : Term
        tjH = ap1 thmT y_h_r
        tjT : Term
        tjT = ap1 thmT payT_T
        a : Term
        a = ap2 Pair tagCode_ruleInst (ap2 Pair payVarX (ap2 Pair y_h_r payT_T))
        codeFP : Term
        codeFP = codeP
        argsPair : Term
        argsPair = ap2 Pair payVarX payT_T
        eVarX : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payVarX))
        eVarX = liftCompFstSnd_evalPair tagCode_ruleInst payVarX
                  (ap2 Pair y_h_r payT_T) bb
        eT : Deriv (atomic (eqn (ap2 (Lift (Comp Snd (Comp Snd Snd))) a bb) payT_T))
        eT = liftSndSndSnd_evalPair3 tagCode_ruleInst payVarX y_h_r payT_T bb
        eARGS : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Lift (Comp Snd (Comp Snd Snd)))
                    Pair) a bb)
          argsPair))
        eARGS = pairOfFan_eval (Lift (Comp Fst Snd))
                               (Lift (Comp Snd (Comp Snd Snd)))
                               a bb payVarX payT_T eVarX eT
        ePost = postSndBody_eval (Comp Fst Snd) a bb
        eDist = cong1 (Comp Fst Snd) distH
        outerPair : Term
        outerPair = ap2 Pair tjV (ap2 Pair tjH tjT)
        eUnfFS = axComp Fst Snd outerPair
        eSnd = axSnd tjV (ap2 Pair tjH tjT)
        eFstSnd = cong1 Fst eSnd
        eCompFS_to_FstInner = ruleTrans eUnfFS eFstSnd
        eInnerFst = axFst tjH tjT
        eCompFS_to_tjH = ruleTrans eCompFS_to_FstInner eInnerFst
        eCODEP_to_tjH : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb) tjH))
        eCODEP_to_tjH = ruleTrans ePost (ruleTrans eDist eCompFS_to_tjH)
        eCODEP : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb) codeFP))
        eCODEP = ruleTrans eCODEP_to_tjH d_h
        eFanBody : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
          (ap2 subT
            (ap2 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Snd (Comp Snd Snd)))
                      Pair) a bb)
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))))
        eFanBody = axFan (Fan (Lift (Comp Fst Snd))
                              (Lift (Comp Snd (Comp Snd Snd)))
                              Pair)
                         (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair)
                         subT a bb
        eL : Deriv (atomic (eqn
          (ap2 subT
            (ap2 (Fan (Lift (Comp Fst Snd))
                      (Lift (Comp Snd (Comp Snd Snd)))
                      Pair) a bb)
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))
          (ap2 subT argsPair
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))))
        eL = congL subT (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb) eARGS
        eR : Deriv (atomic (eqn
          (ap2 subT argsPair
            (ap2 (Post (Comp (Comp Fst Snd) (Comp Snd Snd)) Pair) a bb))
          (ap2 subT argsPair codeFP)))
        eR = congR subT argsPair eCODEP
    in ruleTrans eFanBody (ruleTrans eL eR)

  ------------------------------------------------------------------
  -- thmTDispRuleInst_param : full parametric dispatch for the sub-rule
  -- clause of th's defining equation (Guard Def 12 line 2).
  --
  -- Mirrors thmTDispRuleInst (closed form) but takes:
  --   * n : Nat (variable index, closed; e.g. 1 for x_1)
  --   * tT xT : Term (substituted term, proof index — both open OK)
  --   * xShape : Sigma Term \ y' -> Sigma Term \ x' ->
  --       Deriv (Fst xT = Pair x' y')   (analog of Df_shape)
  --
  -- Output: Deriv (thmT (subProofEnc) = subT (varCode, tT) (thmT xT))
  --
  -- subProofEnc structure:
  --   ap2 Pair tagCode_ruleInst
  --     (ap2 Pair (reify (code (var n))) (ap2 Pair xT tT))
  --
  -- The output subT-form, by sb's defining equation, equals
  --   sb (Pair tT (reify (natCode n))) (thmT xT)
  -- giving the asymmetric Theorem 13-style encoded equation
  -- "th(num x) = th(x)" parametric in the proof index xT.

  thmTDispRuleInst_param : (n : Nat) (tT xT : Term)
    (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst xT) (ap2 Pair x' y')))))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleInst
                  (ap2 Pair (reify (code (var n))) (ap2 Pair xT tT))))
      (ap2 subT (ap2 Pair (reify (code (var n))) tT) (ap1 thmT xT))))
  thmTDispRuleInst_param n tT xT xShape =
    let payVarX : Term
        payVarX = reify (code (var n))
        payT : Term
        payT = ap2 Pair payVarX (ap2 Pair xT tT)
        a    : Term
        a    = ap2 Pair tagCode_ruleInst payT
        b    : Term
        b    = ap2 Pair (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)

        e1   = dispatchOpens tagMp payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleInst payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleInst refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleInst payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleInst refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleInst payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleInst refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleInst payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleInst refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleInst payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleInst refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleInst payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleInst refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleInst payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleInst refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleInst payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleInst refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleInst payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleInst refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleInst payT b body_axZ        next_axKT
                  (teqDiff tagAxKT        tagRuleInst refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleInst payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleInst refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleInst payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleInst refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleInst payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleInst refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleInst payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleInst refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleInst payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleInst refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleInst payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleInst refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleInst payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleInst refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleInst payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleInst refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleInst payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleInst refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleInst payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleInst refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleInst payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleInst refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleInst payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleInst refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleInst payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleInst refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_ruleInst payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagRuleInst refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_ruleInst payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagRuleInst refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_ruleInst payT b body_congL       next_congL
                  (teqDiff tagCongL       tagRuleInst refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_ruleInst payT b body_congR       next_congR
                  (teqDiff tagCongR       tagRuleInst refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_ruleInst payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagRuleInst refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_ruleInst payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagRuleInst refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_ruleInst payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagRuleInst refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_ruleInst payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagRuleInst refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_ruleInst payT b body_axK         next_axK
                  (teqDiff tagAxK         tagRuleInst refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_ruleInst payT b body_axS         next_axS
                  (teqDiff tagAxS         tagRuleInst refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_ruleInst payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagRuleInst refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_ruleInst payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagRuleInst refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_ruleInst payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagRuleInst refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_ruleInst payT b body_mp          next_mp
                  (teqDiff tagMp          tagRuleInst refl)
        hh   = hitAtTag  (natCode tagRuleInst)    tagCode_ruleInst payT b body_ruleInst    next_ruleInst
                  (teqEq tagRuleInst)

        -- distH derivation: parametric, two thmTDistrib_param applications.
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
        shapeV = fstReifyCodeVar n
        distrib1 = thmTDistrib_param payVarX (ap2 Pair xT tT)
                                     {x' = fst shapeV} (fst (snd shapeV))
                                     (snd (snd shapeV))
        distrib2 = thmTDistrib_param xT tT
                                     {x' = fst (snd xShape)} (fst xShape)
                                     (snd (snd xShape))
        distrib2_lifted = congR Pair (ap1 thmT payVarX) distrib2
        distrib_full = ruleTrans distrib1 distrib2_lifted
        distH = ruleTrans sndB_unfold distrib_full

        -- d_h: thmT xT = thmT xT (refl).  Yields codeP = thmT xT.
        be = body_ruleInst_eval_param n tT xT b (ap1 thmT xT)
                                       distH (axRefl (ap1 thmT xT))

    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- body_ruleInst2_eval: like body_ruleInst_eval but for the
  -- simultaneous double substitution (tagRuleInst2 / encRuleInst2).
  --
  -- Payload structure (a):
  --   a = Pair tagCode_ruleInst2
  --        (Pair (reify(code(var xA)))
  --          (Pair (reify(code(var xB)))
  --            (Pair (reify y_h)
  --              (Pair (reify(code tA)) (reify(code tB))))))
  --
  -- Snd bb decomposes via thmTDistrib (5 children):
  --   Snd bb = Pair (thmT xACode)
  --             (Pair (thmT xBCode)
  --               (Pair (thmT y_h_r)
  --                 (Pair (thmT tACode) (thmT tBCode))))
  --
  -- d_h supplies thmT y_h_r = reify(codeFormula P).
  --
  -- The codeCommutes2 Eq is supplied as a parameter; callers discharge
  -- it for their concrete substituents.

  body_ruleInst2_eval : (xA xB : Nat) (tA tB : Term) (P : Formula)
                        (y_h : Tree) (bb tailT : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
      (ap2 Pair (ap1 thmT (reify (code (var xA))))
       (ap2 Pair (ap1 thmT (reify (code (var xB))))
        (ap2 Pair (ap1 thmT (reify y_h)) tailT))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h)) (reify (codeFormula P)))) ->
    Eq (codeFormula (substF xA tA (substF xB tB P)))
       (codedSubst2 (code tA) (code tB) (code (var xA)) (code (var xB))
                    (codeFormula P)) ->
    Deriv (atomic (eqn
      (ap2 body_ruleInst2
            (ap2 Pair tagCode_ruleInst2
                  (reify (nd (code (var xA))
                             (nd (code (var xB))
                                 (nd y_h (nd (code tA) (code tB)))))))
            bb)
      (reify (outRuleInst2 xA xB tA tB P))))
  body_ruleInst2_eval xA xB tA tB P y_h bb tailT distH d_h codeCommEq =
    let payVarA : Term
        payVarA = reify (code (var xA))
        payVarB : Term
        payVarB = reify (code (var xB))
        y_h_r : Term
        y_h_r = reify y_h
        payTA : Term
        payTA = reify (code tA)
        payTB : Term
        payTB = reify (code tB)
        tjVA : Term
        tjVA = ap1 thmT payVarA
        tjVB : Term
        tjVB = ap1 thmT payVarB
        tjH : Term
        tjH = ap1 thmT y_h_r
        a : Term
        a = ap2 Pair tagCode_ruleInst2
              (ap2 Pair payVarA
                (ap2 Pair payVarB
                  (ap2 Pair y_h_r (ap2 Pair payTA payTB))))
        codeFP : Term
        codeFP = reify (codeFormula P)

        -- ARGS_extractor: build Pair (Pair payVarA payTA) (Pair payVarB payTB).
        -- Four Lift-eval steps + 3 pairOfFan_eval combinations.

        e_xA : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payVarA))
        e_xA = liftCompFstSnd_evalPair tagCode_ruleInst2 payVarA
                  (ap2 Pair payVarB
                    (ap2 Pair y_h_r (ap2 Pair payTA payTB))) bb

        e_tA : Deriv (atomic (eqn
          (ap2 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) a bb)
          payTA))
        e_tA = liftFstSndSndSndSnd_evalPair5 tagCode_ruleInst2
                  payVarA payVarB y_h_r payTA payTB bb

        e_xB : Deriv (atomic (eqn
          (ap2 (Lift (Comp Fst (Comp Snd Snd))) a bb) payVarB))
        e_xB = liftFstSndSnd_evalPair3 tagCode_ruleInst2 payVarA payVarB
                  (ap2 Pair y_h_r (ap2 Pair payTA payTB)) bb

        e_tB : Deriv (atomic (eqn
          (ap2 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) a bb)
          payTB))
        e_tB = liftSndSndSndSndSnd_evalPair5 tagCode_ruleInst2
                  payVarA payVarB y_h_r payTA payTB bb

        innerA : Term
        innerA = ap2 Pair payVarA payTA
        innerB : Term
        innerB = ap2 Pair payVarB payTB
        argsPair : Term
        argsPair = ap2 Pair innerA innerB

        eInnerA : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    Pair) a bb)
          innerA))
        eInnerA = pairOfFan_eval (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 a bb payVarA payTA e_xA e_tA

        eInnerB : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    Pair) a bb)
          innerB))
        eInnerB = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 a bb payVarB payTB e_xB e_tB

        argsExtractor : Fun2
        argsExtractor =
          Fan
            (Fan (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                 Pair)
            (Fan (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                 Pair)
            Pair

        eARGS : Deriv (atomic (eqn (ap2 argsExtractor a bb) argsPair))
        eARGS = pairOfFan_eval
          (Fan (Lift (Comp Fst Snd))
               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
               Pair)
          (Fan (Lift (Comp Fst (Comp Snd Snd)))
               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
               Pair)
          a bb innerA innerB eInnerA eInnerB

        -- CODEP_extractor: Post (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair.
        -- Evaluates to Fst(Snd(Snd(Snd bb))) = tjH (via distH).

        codepExtractor : Fun2
        codepExtractor =
          Post (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair

        ePostUnf : Deriv (atomic (eqn (ap2 codepExtractor a bb)
          (ap1 (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) (ap2 Pair a bb))))
        ePostUnf = axPost (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair a bb

        -- Reduce the outer Comp.
        eUnf1 : Deriv (atomic (eqn
          (ap1 (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) (ap2 Pair a bb))
          (ap1 (Comp Fst Snd) (ap1 (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)))))
        eUnf1 = axComp (Comp Fst Snd) (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)

        -- (Comp Snd (Comp Snd Snd))(Pair a bb) = Snd(Snd(Snd(Pair a bb))) = Snd(Snd bb).
        eUnf2 : Deriv (atomic (eqn
          (ap1 (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb))
          (ap1 Snd (ap1 (Comp Snd Snd) (ap2 Pair a bb)))))
        eUnf2 = axComp Snd (Comp Snd Snd) (ap2 Pair a bb)

        eUnf3 : Deriv (atomic (eqn
          (ap1 (Comp Snd Snd) (ap2 Pair a bb))
          (ap1 Snd (ap1 Snd (ap2 Pair a bb)))))
        eUnf3 = axComp Snd Snd (ap2 Pair a bb)

        eUnf4 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair a bb)) bb))
        eUnf4 = axSnd a bb

        eUnf5 : Deriv (atomic (eqn (ap1 Snd (ap1 Snd (ap2 Pair a bb))) (ap1 Snd bb)))
        eUnf5 = cong1 Snd eUnf4

        eUnf3_to_Sndbb : Deriv (atomic (eqn
          (ap1 (Comp Snd Snd) (ap2 Pair a bb)) (ap1 Snd bb)))
        eUnf3_to_Sndbb = ruleTrans eUnf3 eUnf5

        eUnf2_to_SndSndbb : Deriv (atomic (eqn
          (ap1 (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb))
          (ap1 Snd (ap1 Snd bb))))
        eUnf2_to_SndSndbb = ruleTrans eUnf2 (cong1 Snd eUnf3_to_Sndbb)

        -- Then push (Comp Fst Snd) outside to get Fst(Snd(Snd(Snd bb))).
        eOuter : Deriv (atomic (eqn
          (ap1 (Comp Fst Snd) (ap1 (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)))
          (ap1 (Comp Fst Snd) (ap1 Snd (ap1 Snd bb)))))
        eOuter = cong1 (Comp Fst Snd) eUnf2_to_SndSndbb

        -- ePostUnf-chain so far: codepExtractor a bb = (Comp Fst Snd)(Snd(Snd bb)).
        ePostBase : Deriv (atomic (eqn
          (ap2 codepExtractor a bb)
          (ap1 (Comp Fst Snd) (ap1 Snd (ap1 Snd bb)))))
        ePostBase = ruleTrans ePostUnf (ruleTrans eUnf1 eOuter)

        -- Now distH: Snd bb = Pair tjVA (Pair tjVB (Pair tjH (Pair tjTA tjTB))).
        -- So Snd(Snd bb) = Snd(Pair tjVA (...)) = Pair tjVB (Pair tjH (Pair tjTA tjTB)),
        -- and (Comp Fst Snd)(that) = Fst(Snd(that)) = Fst(Pair tjH (...)) = tjH.

        eSndDist : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
          (ap1 Snd (ap2 Pair tjVA (ap2 Pair tjVB (ap2 Pair tjH tailT))))))
        eSndDist = cong1 Snd distH

        eSndOfPair : Deriv (atomic (eqn
          (ap1 Snd (ap2 Pair tjVA (ap2 Pair tjVB (ap2 Pair tjH tailT))))
          (ap2 Pair tjVB (ap2 Pair tjH tailT))))
        eSndOfPair = axSnd tjVA (ap2 Pair tjVB (ap2 Pair tjH tailT))

        eSndSndbb : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
          (ap2 Pair tjVB (ap2 Pair tjH tailT))))
        eSndSndbb = ruleTrans eSndDist eSndOfPair

        ePushFstSnd : Deriv (atomic (eqn
          (ap1 (Comp Fst Snd) (ap1 Snd (ap1 Snd bb)))
          (ap1 (Comp Fst Snd) (ap2 Pair tjVB (ap2 Pair tjH tailT)))))
        ePushFstSnd = cong1 (Comp Fst Snd) eSndSndbb

        -- (Comp Fst Snd) of that pair: Fst(Snd(Pair tjVB rest)) = Fst(rest) = tjH.
        eUnfFS : Deriv (atomic (eqn
          (ap1 (Comp Fst Snd) (ap2 Pair tjVB (ap2 Pair tjH tailT)))
          (ap1 Fst (ap1 Snd (ap2 Pair tjVB (ap2 Pair tjH tailT))))))
        eUnfFS = axComp Fst Snd (ap2 Pair tjVB (ap2 Pair tjH tailT))

        eSndOfPair2 : Deriv (atomic (eqn
          (ap1 Snd (ap2 Pair tjVB (ap2 Pair tjH tailT)))
          (ap2 Pair tjH tailT)))
        eSndOfPair2 = axSnd tjVB (ap2 Pair tjH tailT)

        eFstSnd : Deriv (atomic (eqn
          (ap1 Fst (ap1 Snd (ap2 Pair tjVB (ap2 Pair tjH tailT))))
          (ap1 Fst (ap2 Pair tjH tailT))))
        eFstSnd = cong1 Fst eSndOfPair2

        eFstOfPair : Deriv (atomic (eqn
          (ap1 Fst (ap2 Pair tjH tailT)) tjH))
        eFstOfPair = axFst tjH tailT

        eFinalToTjH : Deriv (atomic (eqn
          (ap1 (Comp Fst Snd) (ap2 Pair tjVB (ap2 Pair tjH tailT)))
          tjH))
        eFinalToTjH = ruleTrans eUnfFS (ruleTrans eFstSnd eFstOfPair)

        eCODEP_to_tjH : Deriv (atomic (eqn (ap2 codepExtractor a bb) tjH))
        eCODEP_to_tjH = ruleTrans ePostBase (ruleTrans ePushFstSnd eFinalToTjH)

        eCODEP : Deriv (atomic (eqn (ap2 codepExtractor a bb) codeFP))
        eCODEP = ruleTrans eCODEP_to_tjH d_h

        -- Apply axFan to body_ruleInst2.
        eFanBody : Deriv (atomic (eqn (ap2 body_ruleInst2 a bb)
          (ap2 subT2 (ap2 argsExtractor a bb) (ap2 codepExtractor a bb))))
        eFanBody = axFan argsExtractor codepExtractor subT2 a bb

        -- Rewrite first subT2 arg.
        eL : Deriv (atomic (eqn
          (ap2 subT2 (ap2 argsExtractor a bb) (ap2 codepExtractor a bb))
          (ap2 subT2 argsPair (ap2 codepExtractor a bb))))
        eL = congL subT2 (ap2 codepExtractor a bb) eARGS

        -- Rewrite second subT2 arg.
        eR : Deriv (atomic (eqn
          (ap2 subT2 argsPair (ap2 codepExtractor a bb))
          (ap2 subT2 argsPair codeFP)))
        eR = congR subT2 argsPair eCODEP

        eBody_to_subT2 : Deriv (atomic (eqn (ap2 body_ruleInst2 a bb)
          (ap2 subT2 argsPair codeFP)))
        eBody_to_subT2 = ruleTrans eFanBody (ruleTrans eL eR)

        -- subTDef2: subT2 args codeFP = reify (codedSubst2 (code tA) (code tB) ...).
        eSubT2 : Deriv (atomic (eqn (ap2 subT2 argsPair codeFP)
          (reify (codedSubst2 (code tA) (code tB)
                              (code (var xA)) (code (var xB))
                              (codeFormula P)))))
        eSubT2 = subTDef2 xA xB (code tA) (code tB) (codeFormula P)

        eBody_to_codedSubst2 : Deriv (atomic (eqn (ap2 body_ruleInst2 a bb)
          (reify (codedSubst2 (code tA) (code tB)
                              (code (var xA)) (code (var xB))
                              (codeFormula P)))))
        eBody_to_codedSubst2 = ruleTrans eBody_to_subT2 eSubT2

        treeEqUser : Eq (codedSubst2 (code tA) (code tB)
                                     (code (var xA)) (code (var xB))
                                     (codeFormula P))
                        (codeFormula (substF xA tA (substF xB tB P)))
        treeEqUser = eqSym codeCommEq

    in eqSubst (\ T -> Deriv (atomic (eqn (ap2 body_ruleInst2 a bb) (reify T))))
               treeEqUser eBody_to_codedSubst2

  ------------------------------------------------------------------
  -- thmTDispRuleInst2: full closed-form dispatch for the simultaneous
  -- double-substitution proof-code.  43 skipAtTag + 1 hitAtTag chain.

  thmTDispRuleInst2 : (xA xB : Nat) (tA tB : Term) (P : Formula)
                      (y_h : Tree) (y_h' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula P)))) ->
    Eq (codeFormula (substF xA tA (substF xB tB P)))
       (codedSubst2 (code tA) (code tB) (code (var xA)) (code (var xB))
                    (codeFormula P)) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst2 xA xB tA tB y_h)))
                       (reify (outRuleInst2 xA xB tA tB P))))
  thmTDispRuleInst2 xA xB tA tB P y_h y_h' shape_h d_h codeCommEq =
    let payT = reify (nd (code (var xA))
                         (nd (code (var xB))
                             (nd y_h (nd (code tA) (code tB)))))
        a    = ap2 Pair tagCode_ruleInst2 payT
        b    = ap2 Pair (ap1 thmT tagCode_ruleInst2) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfNL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleInst2 payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleInst2 refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleInst2 payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleInst2 refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleInst2 payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleInst2 refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleInst2 payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleInst2 refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleInst2 payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleInst2 refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleInst2 payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleInst2 refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleInst2 payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleInst2 refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleInst2 payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleInst2 refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleInst2 payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleInst2 refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleInst2 payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagRuleInst2 refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleInst2 payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleInst2 refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleInst2 payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleInst2 refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleInst2 payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleInst2 refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleInst2 payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleInst2 refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleInst2 payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleInst2 refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleInst2 payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleInst2 refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleInst2 payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleInst2 refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleInst2 payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleInst2 refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleInst2 payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleInst2 refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleInst2 payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleInst2 refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleInst2 payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleInst2 refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleInst2 payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleInst2 refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleInst2 payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleInst2 refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_ruleInst2 payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagRuleInst2 refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_ruleInst2 payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagRuleInst2 refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_ruleInst2 payT b body_congL       next_congL
                  (teqDiff tagCongL       tagRuleInst2 refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_ruleInst2 payT b body_congR       next_congR
                  (teqDiff tagCongR       tagRuleInst2 refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_ruleInst2 payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagRuleInst2 refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_ruleInst2 payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagRuleInst2 refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_ruleInst2 payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagRuleInst2 refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_ruleInst2 payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagRuleInst2 refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_ruleInst2 payT b body_axK         next_axK
                  (teqDiff tagAxK         tagRuleInst2 refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_ruleInst2 payT b body_axS         next_axS
                  (teqDiff tagAxS         tagRuleInst2 refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_ruleInst2 payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagRuleInst2 refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_ruleInst2 payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagRuleInst2 refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_ruleInst2 payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagRuleInst2 refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_ruleInst2 payT b body_mp          next_mp
                  (teqDiff tagMp          tagRuleInst2 refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_ruleInst2 payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagRuleInst2 refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_ruleInst2 payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagRuleInst2 refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_ruleInst2 payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagRuleInst2 refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_ruleInst2 payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagRuleInst2 refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_ruleInst2 payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagRuleInst2 refl)
        s43  = skipAtTag (natCode tagAxIfLfNL)    tagCode_ruleInst2 payT b body_axIfLfNL    next_axIfLfNL
                  (teqDiff tagAxIfLfNL    tagRuleInst2 refl)
        hh   = hitAtTag  (natCode tagRuleInst2)   tagCode_ruleInst2 payT b body_ruleInst2   fbBody
                  (teqEq tagRuleInst2)

        -- distH: 3-fold thmTDistrib decomposition of Snd b.  Deepest
        -- term left as opaque tailT = thmT (reify (nd (code tA) (code tB))),
        -- so we don't need a shape proof for tA / tB.
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleInst2) (ap1 thmT payT)
        shapeA = fstReifyCodeVar xA
        shapeB = fstReifyCodeVar xB
        d1 = thmTDistrib (code (var xA))
                         (nd (code (var xB))
                             (nd y_h (nd (code tA) (code tB))))
                         {x' = fst shapeA} (fst (snd shapeA)) (snd (snd shapeA))
        d2 = thmTDistrib (code (var xB))
                         (nd y_h (nd (code tA) (code tB)))
                         {x' = fst shapeB} (fst (snd shapeB)) (snd (snd shapeB))
        d3 = thmTDistrib y_h (nd (code tA) (code tB)) y_h' shape_h
        d3_lifted = congR Pair (ap1 thmT (reify (code (var xB)))) d3
        d2_combined = ruleTrans d2 d3_lifted
        d2_lifted = congR Pair (ap1 thmT (reify (code (var xA)))) d2_combined
        d1_combined = ruleTrans d1 d2_lifted
        distH = ruleTrans sndB_unfold d1_combined

        tailT = ap1 thmT (reify (nd (code tA) (code tB)))

        be = body_ruleInst2_eval xA xB tA tB P y_h b tailT distH d_h codeCommEq

    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- body_ruleInst2_eval_param: parametric variant of body_ruleInst2_eval.
  -- Takes Term substituents tA, tB and Term proof index xT.  Returns
  -- the subT2-form (without applying subTDef2 + codeCommutes2), so
  -- callers can plug in their own concrete reductions.

  body_ruleInst2_eval_param :
    (nA nB : Nat) (tA tB xT : Term) (bb : Term) (codeP : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
      (ap2 Pair (ap1 thmT (reify (code (var nA))))
       (ap2 Pair (ap1 thmT (reify (code (var nB))))
        (ap2 Pair (ap1 thmT xT)
                  (ap1 thmT (ap2 Pair tA tB))))))) ->
    Deriv (atomic (eqn (ap1 thmT xT) codeP)) ->
    Deriv (atomic (eqn
      (ap2 body_ruleInst2
            (ap2 Pair tagCode_ruleInst2
                  (ap2 Pair (reify (code (var nA)))
                    (ap2 Pair (reify (code (var nB)))
                      (ap2 Pair xT (ap2 Pair tA tB)))))
            bb)
      (ap2 subT2 (ap2 Pair (ap2 Pair (reify (code (var nA))) tA)
                            (ap2 Pair (reify (code (var nB))) tB))
                  codeP)))
  body_ruleInst2_eval_param nA nB tA tB xT bb codeP distH d_h =
    let payVarA : Term
        payVarA = reify (code (var nA))
        payVarB : Term
        payVarB = reify (code (var nB))
        tjVA : Term
        tjVA = ap1 thmT payVarA
        tjVB : Term
        tjVB = ap1 thmT payVarB
        tjH : Term
        tjH = ap1 thmT xT
        tailT : Term
        tailT = ap1 thmT (ap2 Pair tA tB)
        a : Term
        a = ap2 Pair tagCode_ruleInst2
              (ap2 Pair payVarA
                (ap2 Pair payVarB
                  (ap2 Pair xT (ap2 Pair tA tB))))

        e_xA : Deriv (atomic (eqn (ap2 (Lift (Comp Fst Snd)) a bb) payVarA))
        e_xA = liftCompFstSnd_evalPair tagCode_ruleInst2 payVarA
                  (ap2 Pair payVarB
                    (ap2 Pair xT (ap2 Pair tA tB))) bb

        e_tA : Deriv (atomic (eqn
          (ap2 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd))))) a bb)
          tA))
        e_tA = liftFstSndSndSndSnd_evalPair5 tagCode_ruleInst2
                  payVarA payVarB xT tA tB bb

        e_xB : Deriv (atomic (eqn
          (ap2 (Lift (Comp Fst (Comp Snd Snd))) a bb) payVarB))
        e_xB = liftFstSndSnd_evalPair3 tagCode_ruleInst2 payVarA payVarB
                  (ap2 Pair xT (ap2 Pair tA tB)) bb

        e_tB : Deriv (atomic (eqn
          (ap2 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd))))) a bb)
          tB))
        e_tB = liftSndSndSndSndSnd_evalPair5 tagCode_ruleInst2
                  payVarA payVarB xT tA tB bb

        innerA : Term
        innerA = ap2 Pair payVarA tA
        innerB : Term
        innerB = ap2 Pair payVarB tB
        argsPair : Term
        argsPair = ap2 Pair innerA innerB

        eInnerA : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst Snd))
                    (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    Pair) a bb)
          innerA))
        eInnerA = pairOfFan_eval (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 a bb payVarA tA e_xA e_tA

        eInnerB : Deriv (atomic (eqn
          (ap2 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                    (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                    Pair) a bb)
          innerB))
        eInnerB = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                                 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                                 a bb payVarB tB e_xB e_tB

        argsExtractor : Fun2
        argsExtractor =
          Fan
            (Fan (Lift (Comp Fst Snd))
                 (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
                 Pair)
            (Fan (Lift (Comp Fst (Comp Snd Snd)))
                 (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
                 Pair)
            Pair

        eARGS : Deriv (atomic (eqn (ap2 argsExtractor a bb) argsPair))
        eARGS = pairOfFan_eval
          (Fan (Lift (Comp Fst Snd))
               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
               Pair)
          (Fan (Lift (Comp Fst (Comp Snd Snd)))
               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
               Pair)
          a bb innerA innerB eInnerA eInnerB

        codepExtractor : Fun2
        codepExtractor =
          Post (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair

        ePostUnf : Deriv (atomic (eqn (ap2 codepExtractor a bb)
          (ap1 (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) (ap2 Pair a bb))))
        ePostUnf = axPost (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair a bb

        eUnf1 = axComp (Comp Fst Snd) (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)
        eUnf2 = axComp Snd (Comp Snd Snd) (ap2 Pair a bb)
        eUnf3 = axComp Snd Snd (ap2 Pair a bb)
        eUnf4 = axSnd a bb
        eUnf5 = cong1 Snd eUnf4
        eUnf3_to_Sndbb = ruleTrans eUnf3 eUnf5
        eUnf2_to_SndSndbb = ruleTrans eUnf2 (cong1 Snd eUnf3_to_Sndbb)
        eOuter = cong1 (Comp Fst Snd) eUnf2_to_SndSndbb

        ePostBase : Deriv (atomic (eqn
          (ap2 codepExtractor a bb)
          (ap1 (Comp Fst Snd) (ap1 Snd (ap1 Snd bb)))))
        ePostBase = ruleTrans ePostUnf (ruleTrans eUnf1 eOuter)

        eSndDist = cong1 Snd distH
        eSndOfPair = axSnd tjVA (ap2 Pair tjVB (ap2 Pair tjH tailT))
        eSndSndbb = ruleTrans eSndDist eSndOfPair
        ePushFstSnd = cong1 (Comp Fst Snd) eSndSndbb

        eUnfFS = axComp Fst Snd (ap2 Pair tjVB (ap2 Pair tjH tailT))
        eSndOfPair2 = axSnd tjVB (ap2 Pair tjH tailT)
        eFstSnd = cong1 Fst eSndOfPair2
        eFstOfPair = axFst tjH tailT
        eFinalToTjH = ruleTrans eUnfFS (ruleTrans eFstSnd eFstOfPair)

        eCODEP_to_tjH = ruleTrans ePostBase (ruleTrans ePushFstSnd eFinalToTjH)
        eCODEP = ruleTrans eCODEP_to_tjH d_h

        eFanBody = axFan argsExtractor codepExtractor subT2 a bb
        eL = congL subT2 (ap2 codepExtractor a bb) eARGS
        eR = congR subT2 argsPair eCODEP
    in ruleTrans eFanBody (ruleTrans eL eR)

  ------------------------------------------------------------------
  -- thmTDispRuleInst2_param: full parametric dispatch for the
  -- simultaneous double-substitution proof code.  Mirrors
  -- thmTDispRuleInst_param (single substitution) but takes TWO
  -- runtime substituent Terms.

  thmTDispRuleInst2_param : (nA nB : Nat) (tA tB xT : Term)
    (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst xT) (ap2 Pair x' y')))))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleInst2
                  (ap2 Pair (reify (code (var nA)))
                    (ap2 Pair (reify (code (var nB)))
                      (ap2 Pair xT (ap2 Pair tA tB))))))
      (ap2 subT2 (ap2 Pair (ap2 Pair (reify (code (var nA))) tA)
                            (ap2 Pair (reify (code (var nB))) tB))
                  (ap1 thmT xT))))
  thmTDispRuleInst2_param nA nB tA tB xT xShape =
    let payVarA : Term
        payVarA = reify (code (var nA))
        payVarB : Term
        payVarB = reify (code (var nB))
        payT : Term
        payT = ap2 Pair payVarA
                 (ap2 Pair payVarB
                   (ap2 Pair xT (ap2 Pair tA tB)))
        a    : Term
        a    = ap2 Pair tagCode_ruleInst2 payT
        b    : Term
        b    = ap2 Pair (ap1 thmT tagCode_ruleInst2) (ap1 thmT payT)

        e1   = dispatchOpens tagAxIfLfNL payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_ruleInst2 payT b body_axI         next_axI
                  (teqDiff tagAxI         tagRuleInst2 refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_ruleInst2 payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagRuleInst2 refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_ruleInst2 payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagRuleInst2 refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_ruleInst2 payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagRuleInst2 refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_ruleInst2 payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagRuleInst2 refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_ruleInst2 payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagRuleInst2 refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_ruleInst2 payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagRuleInst2 refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_ruleInst2 payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagRuleInst2 refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_ruleInst2 payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagRuleInst2 refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_ruleInst2 payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagRuleInst2 refl)
        s11  = skipAtTag (natCode tagAxRecLf)     tagCode_ruleInst2 payT b body_axRecLf     next_axRecLf
                  (teqDiff tagAxRecLf     tagRuleInst2 refl)
        s12  = skipAtTag (natCode tagAxRecNd)     tagCode_ruleInst2 payT b body_axRecNd     next_axRecNd
                  (teqDiff tagAxRecNd     tagRuleInst2 refl)
        s13  = skipAtTag (natCode tagAxRecPLf)    tagCode_ruleInst2 payT b body_axRecPLf    next_axRecPLf
                  (teqDiff tagAxRecPLf    tagRuleInst2 refl)
        s14  = skipAtTag (natCode tagAxRecPNd)    tagCode_ruleInst2 payT b body_axRecPNd    next_axRecPNd
                  (teqDiff tagAxRecPNd    tagRuleInst2 refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_ruleInst2 payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagRuleInst2 refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_ruleInst2 payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagRuleInst2 refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_ruleInst2 payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagRuleInst2 refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_ruleInst2 payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagRuleInst2 refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_ruleInst2 payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagRuleInst2 refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_ruleInst2 payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagRuleInst2 refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_ruleInst2 payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagRuleInst2 refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_ruleInst2 payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagRuleInst2 refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_ruleInst2 payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagRuleInst2 refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_ruleInst2 payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagRuleInst2 refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_ruleInst2 payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagRuleInst2 refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_ruleInst2 payT b body_congL       next_congL
                  (teqDiff tagCongL       tagRuleInst2 refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_ruleInst2 payT b body_congR       next_congR
                  (teqDiff tagCongR       tagRuleInst2 refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_ruleInst2 payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagRuleInst2 refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_ruleInst2 payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagRuleInst2 refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_ruleInst2 payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagRuleInst2 refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_ruleInst2 payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagRuleInst2 refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_ruleInst2 payT b body_axK         next_axK
                  (teqDiff tagAxK         tagRuleInst2 refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_ruleInst2 payT b body_axS         next_axS
                  (teqDiff tagAxS         tagRuleInst2 refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_ruleInst2 payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagRuleInst2 refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_ruleInst2 payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagRuleInst2 refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_ruleInst2 payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagRuleInst2 refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_ruleInst2 payT b body_mp          next_mp
                  (teqDiff tagMp          tagRuleInst2 refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_ruleInst2 payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagRuleInst2 refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_ruleInst2 payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagRuleInst2 refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_ruleInst2 payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagRuleInst2 refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_ruleInst2 payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagRuleInst2 refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_ruleInst2 payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagRuleInst2 refl)
        s43  = skipAtTag (natCode tagAxIfLfNL)    tagCode_ruleInst2 payT b body_axIfLfNL    next_axIfLfNL
                  (teqDiff tagAxIfLfNL    tagRuleInst2 refl)
        hh   = hitAtTag  (natCode tagRuleInst2)   tagCode_ruleInst2 payT b body_ruleInst2   fbBody
                  (teqEq tagRuleInst2)

        -- distH: parametric, 3 thmTDistrib_param applications.
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleInst2) (ap1 thmT payT)
        shapeA = fstReifyCodeVar nA
        shapeB = fstReifyCodeVar nB
        d1 = thmTDistrib_param payVarA
                               (ap2 Pair payVarB (ap2 Pair xT (ap2 Pair tA tB)))
                               {x' = fst shapeA} (fst (snd shapeA))
                               (snd (snd shapeA))
        d2 = thmTDistrib_param payVarB
                               (ap2 Pair xT (ap2 Pair tA tB))
                               {x' = fst shapeB} (fst (snd shapeB))
                               (snd (snd shapeB))
        d3 = thmTDistrib_param xT (ap2 Pair tA tB)
                               {x' = fst (snd xShape)} (fst xShape)
                               (snd (snd xShape))
        d3_lifted = congR Pair (ap1 thmT payVarB) d3
        d2_combined = ruleTrans d2 d3_lifted
        d2_lifted = congR Pair (ap1 thmT payVarA) d2_combined
        d1_combined = ruleTrans d1 d2_lifted
        distH = ruleTrans sndB_unfold d1_combined

        be = body_ruleInst2_eval_param nA nB tA tB xT b (ap1 thmT xT)
                                        distH (axRefl (ap1 thmT xT))

    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Theorem 12 / Parts/TreeEq.agda parametric variants for the four
  -- TreeEq axioms (LL/LN/NL/NN).  Mirrors the IfLfLL/L/N/NL _param
  -- pattern.  Outputs are spelt out as explicit Pair structures
  -- instead of  reify (outAxTreeEq* ...)  since reify does not
  -- compute on parametric Term inputs.

  -- TreeEqLL : 0 args; output = reify outAxTreeEqLL (closed).
  body_axTreeEqLL_eval_param : (payT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqLL (ap2 Pair tagCode_axTreeEqLL payT) bb)
      (reify outAxTreeEqLL)))
  body_axTreeEqLL_eval_param payT bb =
    liftKT_eval outAxTreeEqLL (ap2 Pair tagCode_axTreeEqLL payT) bb

  thmTDispAxTreeEqLL_param : (payT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axTreeEqLL payT))
      (reify outAxTreeEqLL)))
  thmTDispAxTreeEqLL_param payT =
    let a    = ap2 Pair tagCode_axTreeEqLL payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqLL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxIfLfN payT
        s1   = skipAtTag (natCode tagAxI)       tagCode_axTreeEqLL payT b body_axI       next_axI
                  (teqDiff tagAxI       tagAxTreeEqLL refl)
        s2   = skipAtTag (natCode tagAxFst)     tagCode_axTreeEqLL payT b body_axFst     next_axFst
                  (teqDiff tagAxFst     tagAxTreeEqLL refl)
        s3   = skipAtTag (natCode tagAxSnd)     tagCode_axTreeEqLL payT b body_axSnd     next_axSnd
                  (teqDiff tagAxSnd     tagAxTreeEqLL refl)
        s4   = skipAtTag (natCode tagAxConst)   tagCode_axTreeEqLL payT b body_axConst   next_axConst
                  (teqDiff tagAxConst   tagAxTreeEqLL refl)
        s5   = skipAtTag (natCode tagAxComp)    tagCode_axTreeEqLL payT b body_axComp    next_axComp
                  (teqDiff tagAxComp    tagAxTreeEqLL refl)
        s6   = skipAtTag (natCode tagAxComp2)   tagCode_axTreeEqLL payT b body_axComp2   next_axComp2
                  (teqDiff tagAxComp2   tagAxTreeEqLL refl)
        s7   = skipAtTag (natCode tagAxLift)    tagCode_axTreeEqLL payT b body_axLift    next_axLift
                  (teqDiff tagAxLift    tagAxTreeEqLL refl)
        s8   = skipAtTag (natCode tagAxPost)    tagCode_axTreeEqLL payT b body_axPost    next_axPost
                  (teqDiff tagAxPost    tagAxTreeEqLL refl)
        s9   = skipAtTag (natCode tagAxFan)     tagCode_axTreeEqLL payT b body_axFan     next_axFan
                  (teqDiff tagAxFan     tagAxTreeEqLL refl)
        s10  = skipAtTag (natCode tagAxKT)      tagCode_axTreeEqLL payT b body_axZ      next_axKT
                  (teqDiff tagAxKT      tagAxTreeEqLL refl)
        s11  = skipAtTag (natCode tagAxRecLf)   tagCode_axTreeEqLL payT b body_axRecLf   next_axRecLf
                  (teqDiff tagAxRecLf   tagAxTreeEqLL refl)
        s12  = skipAtTag (natCode tagAxRecNd)   tagCode_axTreeEqLL payT b body_axRecNd   next_axRecNd
                  (teqDiff tagAxRecNd   tagAxTreeEqLL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)  tagCode_axTreeEqLL payT b body_axRecPLf  next_axRecPLf
                  (teqDiff tagAxRecPLf  tagAxTreeEqLL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)  tagCode_axTreeEqLL payT b body_axRecPNd  next_axRecPNd
                  (teqDiff tagAxRecPNd  tagAxTreeEqLL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axTreeEqLL payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxTreeEqLL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)   tagCode_axTreeEqLL payT b body_axIfLfN   next_axIfLfN
                  (teqDiff tagAxIfLfN   tagAxTreeEqLL refl)
        hh   = hitAtTag  (natCode tagAxTreeEqLL) tagCode_axTreeEqLL payT b body_axTreeEqLL next_axTreeEqLL
                  (teqEq tagAxTreeEqLL)
        be   = body_axTreeEqLL_eval_param payT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans hh be)))))))))))))))))

  -- TreeEqLN : 2 args; depth-2 payload.  Parametric in aT, bT.
  body_axTreeEqLN_eval_param : (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqLN (ap2 Pair tagCode_axTreeEqLN (ap2 Pair aT bT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 TreeEq))
            (ap2 Pair O
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT))))))
        (reify (code (ap2 Pair O O))))))
  body_axTreeEqLN_eval_param aT bT bb =
    let payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axTreeEqLN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ooV  = lf
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rhsV = code (ap2 Pair O O)
        K_rhs  = reify K_rhsV
        snd_a  = bodyLiftSndPair tagCode_axTreeEqLN payT bb
        l5 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        l3 = pairOfConst_eval K_ooV
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 a bb (ap2 Pair K_a2 (ap2 Pair K_pair payT)) l4
        l2 = pairOfConst_eval K_teV
                 (Fan (Lift (KT K_oo))
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair) Pair)
                 a bb
                 (ap2 Pair K_oo (ap2 Pair K_a2 (ap2 Pair K_pair payT))) l3
        l1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_te))
                      (Fan (Lift (KT K_oo))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_te (ap2 Pair K_oo
                    (ap2 Pair K_a2 (ap2 Pair K_pair payT)))) l2
        rhs = liftKT_eval K_rhsV a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Lift (KT K_oo))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        Pair) Pair) Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair K_oo
            (ap2 Pair K_a2 (ap2 Pair K_pair payT))))) K_rhs
         l1 rhs

  thmTDispAxTreeEqLN_param : (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axTreeEqLN (ap2 Pair aT bT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 TreeEq))
            (ap2 Pair O
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT))))))
        (reify (code (ap2 Pair O O))))))
  thmTDispAxTreeEqLN_param aT bT =
    let payT = ap2 Pair aT bT
        a    = ap2 Pair tagCode_axTreeEqLN payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqLN) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqLL payT
        s1   = skipAtTag (natCode tagAxI)        tagCode_axTreeEqLN payT b body_axI        next_axI
                  (teqDiff tagAxI        tagAxTreeEqLN refl)
        s2   = skipAtTag (natCode tagAxFst)      tagCode_axTreeEqLN payT b body_axFst      next_axFst
                  (teqDiff tagAxFst      tagAxTreeEqLN refl)
        s3   = skipAtTag (natCode tagAxSnd)      tagCode_axTreeEqLN payT b body_axSnd      next_axSnd
                  (teqDiff tagAxSnd      tagAxTreeEqLN refl)
        s4   = skipAtTag (natCode tagAxConst)    tagCode_axTreeEqLN payT b body_axConst    next_axConst
                  (teqDiff tagAxConst    tagAxTreeEqLN refl)
        s5   = skipAtTag (natCode tagAxComp)     tagCode_axTreeEqLN payT b body_axComp     next_axComp
                  (teqDiff tagAxComp     tagAxTreeEqLN refl)
        s6   = skipAtTag (natCode tagAxComp2)    tagCode_axTreeEqLN payT b body_axComp2    next_axComp2
                  (teqDiff tagAxComp2    tagAxTreeEqLN refl)
        s7   = skipAtTag (natCode tagAxLift)     tagCode_axTreeEqLN payT b body_axLift     next_axLift
                  (teqDiff tagAxLift     tagAxTreeEqLN refl)
        s8   = skipAtTag (natCode tagAxPost)     tagCode_axTreeEqLN payT b body_axPost     next_axPost
                  (teqDiff tagAxPost     tagAxTreeEqLN refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axTreeEqLN payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxTreeEqLN refl)
        s10  = skipAtTag (natCode tagAxKT)       tagCode_axTreeEqLN payT b body_axZ       next_axKT
                  (teqDiff tagAxKT       tagAxTreeEqLN refl)
        s11  = skipAtTag (natCode tagAxRecLf)    tagCode_axTreeEqLN payT b body_axRecLf    next_axRecLf
                  (teqDiff tagAxRecLf    tagAxTreeEqLN refl)
        s12  = skipAtTag (natCode tagAxRecNd)    tagCode_axTreeEqLN payT b body_axRecNd    next_axRecNd
                  (teqDiff tagAxRecNd    tagAxTreeEqLN refl)
        s13  = skipAtTag (natCode tagAxRecPLf)   tagCode_axTreeEqLN payT b body_axRecPLf   next_axRecPLf
                  (teqDiff tagAxRecPLf   tagAxTreeEqLN refl)
        s14  = skipAtTag (natCode tagAxRecPNd)   tagCode_axTreeEqLN payT b body_axRecPNd   next_axRecPNd
                  (teqDiff tagAxRecPNd   tagAxTreeEqLN refl)
        s15  = skipAtTag (natCode tagAxIfLfL)    tagCode_axTreeEqLN payT b body_axIfLfL    next_axIfLfL
                  (teqDiff tagAxIfLfL    tagAxTreeEqLN refl)
        s16  = skipAtTag (natCode tagAxIfLfN)    tagCode_axTreeEqLN payT b body_axIfLfN    next_axIfLfN
                  (teqDiff tagAxIfLfN    tagAxTreeEqLN refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL) tagCode_axTreeEqLN payT b body_axTreeEqLL next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL tagAxTreeEqLN refl)
        hh   = hitAtTag  (natCode tagAxTreeEqLN) tagCode_axTreeEqLN payT b body_axTreeEqLN next_axTreeEqLN
                  (teqEq tagAxTreeEqLN)
        be   = body_axTreeEqLN_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans hh be))))))))))))))))))

  -- TreeEqNL : 2 args; depth-2 payload.  Mirror of LN.
  body_axTreeEqNL_eval_param : (aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqNL (ap2 Pair tagCode_axTreeEqNL (ap2 Pair aT bT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 TreeEq))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair aT bT)))
                      O)))
        (reify (code (ap2 Pair O O))))))
  body_axTreeEqNL_eval_param aT bT bb =
    let payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payAT payBT
        a      = ap2 Pair tagCode_axTreeEqNL payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ooV  = lf
        K_oo   = reify K_ooV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rhsV = code (ap2 Pair O O)
        K_rhs  = reify K_rhsV
        snd_a  = bodyLiftSndPair tagCode_axTreeEqNL payT bb
        l5 = pairOfConst_eval K_pairV (Lift Snd) a bb payT snd_a
        l4 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair)) (Lift Snd) Pair) a bb
                 (ap2 Pair K_pair payT) l5
        kOO = liftKT_eval K_ooV a bb
        l3 = pairOfFan_eval
                 (Fan (Lift (KT K_a2))
                      (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                 (Lift (KT K_oo)) a bb
                 (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo
                 l4 kOO
        l2 = pairOfConst_eval K_teV
                 (Fan (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                      (Lift (KT K_oo)) Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo) l3
        l1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_te))
                      (Fan (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                           (Lift (KT K_oo)) Pair) Pair)
                 a bb
                 (ap2 Pair K_te
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo)) l2
        rhs = liftKT_eval K_rhsV a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair)) (Lift Snd) Pair) Pair)
                        (Lift (KT K_oo)) Pair) Pair) Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair K_te
            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair payT)) K_oo))) K_rhs
         l1 rhs

  thmTDispAxTreeEqNL_param : (aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axTreeEqNL (ap2 Pair aT bT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 TreeEq))
            (ap2 Pair (ap2 Pair (reify tagAp2)
                                (ap2 Pair (reify (codeF2 Pair))
                                          (ap2 Pair aT bT)))
                      O)))
        (reify (code (ap2 Pair O O))))))
  thmTDispAxTreeEqNL_param aT bT =
    let payT = ap2 Pair aT bT
        a    = ap2 Pair tagCode_axTreeEqNL payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqNL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqLN payT
        s1   = skipAtTag (natCode tagAxI)        tagCode_axTreeEqNL payT b body_axI        next_axI
                  (teqDiff tagAxI        tagAxTreeEqNL refl)
        s2   = skipAtTag (natCode tagAxFst)      tagCode_axTreeEqNL payT b body_axFst      next_axFst
                  (teqDiff tagAxFst      tagAxTreeEqNL refl)
        s3   = skipAtTag (natCode tagAxSnd)      tagCode_axTreeEqNL payT b body_axSnd      next_axSnd
                  (teqDiff tagAxSnd      tagAxTreeEqNL refl)
        s4   = skipAtTag (natCode tagAxConst)    tagCode_axTreeEqNL payT b body_axConst    next_axConst
                  (teqDiff tagAxConst    tagAxTreeEqNL refl)
        s5   = skipAtTag (natCode tagAxComp)     tagCode_axTreeEqNL payT b body_axComp     next_axComp
                  (teqDiff tagAxComp     tagAxTreeEqNL refl)
        s6   = skipAtTag (natCode tagAxComp2)    tagCode_axTreeEqNL payT b body_axComp2    next_axComp2
                  (teqDiff tagAxComp2    tagAxTreeEqNL refl)
        s7   = skipAtTag (natCode tagAxLift)     tagCode_axTreeEqNL payT b body_axLift     next_axLift
                  (teqDiff tagAxLift     tagAxTreeEqNL refl)
        s8   = skipAtTag (natCode tagAxPost)     tagCode_axTreeEqNL payT b body_axPost     next_axPost
                  (teqDiff tagAxPost     tagAxTreeEqNL refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axTreeEqNL payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxTreeEqNL refl)
        s10  = skipAtTag (natCode tagAxKT)       tagCode_axTreeEqNL payT b body_axZ       next_axKT
                  (teqDiff tagAxKT       tagAxTreeEqNL refl)
        s11  = skipAtTag (natCode tagAxRecLf)    tagCode_axTreeEqNL payT b body_axRecLf    next_axRecLf
                  (teqDiff tagAxRecLf    tagAxTreeEqNL refl)
        s12  = skipAtTag (natCode tagAxRecNd)    tagCode_axTreeEqNL payT b body_axRecNd    next_axRecNd
                  (teqDiff tagAxRecNd    tagAxTreeEqNL refl)
        s13  = skipAtTag (natCode tagAxRecPLf)   tagCode_axTreeEqNL payT b body_axRecPLf   next_axRecPLf
                  (teqDiff tagAxRecPLf   tagAxTreeEqNL refl)
        s14  = skipAtTag (natCode tagAxRecPNd)   tagCode_axTreeEqNL payT b body_axRecPNd   next_axRecPNd
                  (teqDiff tagAxRecPNd   tagAxTreeEqNL refl)
        s15  = skipAtTag (natCode tagAxIfLfL)    tagCode_axTreeEqNL payT b body_axIfLfL    next_axIfLfL
                  (teqDiff tagAxIfLfL    tagAxTreeEqNL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)    tagCode_axTreeEqNL payT b body_axIfLfN    next_axIfLfN
                  (teqDiff tagAxIfLfN    tagAxTreeEqNL refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL) tagCode_axTreeEqNL payT b body_axTreeEqLL next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL tagAxTreeEqNL refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN) tagCode_axTreeEqNL payT b body_axTreeEqLN next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN tagAxTreeEqNL refl)
        hh   = hitAtTag  (natCode tagAxTreeEqNL) tagCode_axTreeEqNL payT b body_axTreeEqNL next_axTreeEqNL
                  (teqEq tagAxTreeEqNL)
        be   = body_axTreeEqNL_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans hh be)))))))))))))))))))

  -- TreeEqNN : 4 args; depth-4 payload.  RHS uses cross-pair structure.
  body_axTreeEqNN_eval_param : (a1T a2T b1T b2T bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axTreeEqNN
            (ap2 Pair tagCode_axTreeEqNN
              (ap2 Pair a1T (ap2 Pair a2T (ap2 Pair b1T b2T)))) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 TreeEq))
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair a1T a2T)))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair b1T b2T))))))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 TreeEq))
                  (ap2 Pair a1T b1T)))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 TreeEq))
                        (ap2 Pair a2T b2T)))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair O O))))))))))))
  body_axTreeEqNN_eval_param a1T a2T b1T b2T bb =
    let payA1  = a1T
        payA2  = a2T
        payB1  = b1T
        payB2  = b2T
        payT   = ap2 Pair payA1 (ap2 Pair payA2 (ap2 Pair payB1 payB2))
        a      = ap2 Pair tagCode_axTreeEqNN payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_teV  = codeF2 TreeEq
        K_te   = reify K_teV
        K_ifLfV = codeF2 IfLf
        K_ifLf = reify K_ifLfV
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_ooV  = lf
        K_oo   = reify K_ooV
        ext_a1 = liftCompFstSnd_evalPair tagCode_axTreeEqNN payA1
                   (ap2 Pair payA2 (ap2 Pair payB1 payB2)) bb
        ext_a2 = liftFstSndSnd_evalPair3 tagCode_axTreeEqNN payA1 payA2
                   (ap2 Pair payB1 payB2) bb
        ext_b1 = liftFstSndSndSnd_evalPair4 tagCode_axTreeEqNN payA1 payA2 payB1 payB2 bb
        ext_b2 = liftSndSndSndSnd_evalPair4 tagCode_axTreeEqNN payA1 payA2 payB1 payB2 bb
        kOO    = liftKT_eval K_ooV a bb
        ----------------------------------------------------------------
        a1a2   = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd Snd))) a bb
                   payA1 payA2 ext_a1 ext_a2
        ka1a2  = pairOfConst_eval K_pairV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd Snd))) Pair)
                   a bb (ap2 Pair payA1 payA2) a1a2
        a_full = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair payA1 payA2)) ka1a2
        b1b2   = pairOfFan_eval (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                   payB1 payB2 ext_b1 ext_b2
        kb1b2  = pairOfConst_eval K_pairV
                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payB1 payB2) b1b2
        b_full = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair payB1 payB2)) kb1b2
        l_inner = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd Snd))) Pair)
                              Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                   Pair)
                              Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                    (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2)))
                    a_full b_full
        l_te   = pairOfConst_eval K_teV
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                              (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2))))
                   l_inner
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_te))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd Snd)))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_te
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2)))))
                     l_te
        ----------------------------------------------------------------
        a1b1   = pairOfFan_eval (Lift (Comp Fst Snd))
                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) a bb
                   payA1 payB1 ext_a1 ext_b1
        kA1B1  = pairOfConst_eval K_teV
                   (Fan (Lift (Comp Fst Snd))
                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payA1 payB1) a1b1
        blkA   = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_te))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_te (ap2 Pair payA1 payB1)) kA1B1
        a2b2   = pairOfFan_eval (Lift (Comp Fst (Comp Snd Snd)))
                   (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                   payA2 payB2 ext_a2 ext_b2
        kA2B2  = pairOfConst_eval K_teV
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                   a bb (ap2 Pair payA2 payB2) a2b2
        blkBin = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_te))
                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                        Pair)
                   a bb (ap2 Pair K_te (ap2 Pair payA2 payB2)) kA2B2
        ooOO   = pairOfFan_eval (Lift (KT K_oo)) (Lift (KT K_oo))
                   a bb K_oo K_oo kOO kOO
        kPOO   = pairOfConst_eval K_pairV
                   (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                   a bb (ap2 Pair K_oo K_oo) ooOO
        blkPOO = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair) Pair)
                   a bb (ap2 Pair K_pair (ap2 Pair K_oo K_oo)) kPOO
        binPOO = pairOfFan_eval
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_te))
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_pair))
                             (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair) Pair)
                        Pair)
                   a bb
                   (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                   (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))
                   blkBin blkPOO
        kBinPOO = pairOfConst_eval K_pairV
                    (Fan (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_te))
                                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                        Pair)
                                   Pair) Pair)
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                                   Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))
                    binPOO
        blkC   = pairOfConst_eval K_a2V
                   (Fan (Lift (KT K_pair))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_te))
                                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                            Pair)
                                       Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (KT K_oo)) (Lift (KT K_oo)) Pair)
                                       Pair) Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_pair
                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))
                   kBinPOO
        r_inner = pairOfFan_eval
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_te))
                              (Fan (Lift (Comp Fst Snd))
                                   (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                              Pair) Pair)
                    (Fan (Lift (KT K_a2))
                         (Fan (Lift (KT K_pair))
                              (Fan (Fan (Lift (KT K_a2))
                                        (Fan (Lift (KT K_te))
                                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                  Pair)
                                             Pair) Pair)
                                   (Fan (Lift (KT K_a2))
                                        (Fan (Lift (KT K_pair))
                                             (Fan (Lift (KT K_oo)) (Lift (KT K_oo))
                                                  Pair)
                                             Pair) Pair)
                                   Pair) Pair) Pair)
                    a bb
                    (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                    (ap2 Pair K_a2
                      (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))))
                    blkA blkC
        r_ifLf  = pairOfConst_eval K_ifLfV
                    (Fan (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_te))
                                   (Fan (Lift (Comp Fst Snd))
                                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                                   Pair) Pair)
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Fan (Lift (KT K_a2))
                                             (Fan (Lift (KT K_te))
                                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                       Pair)
                                                  Pair) Pair)
                                        (Fan (Lift (KT K_a2))
                                             (Fan (Lift (KT K_pair))
                                                  (Fan (Lift (KT K_oo)) (Lift (KT K_oo))
                                                       Pair)
                                                  Pair) Pair)
                                        Pair) Pair) Pair)
                         Pair)
                    a bb
                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                               (ap2 Pair K_a2
                                 (ap2 Pair K_pair
                                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                              (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))))
                    r_inner
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_ifLf))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_te))
                                         (Fan (Lift (Comp Fst Snd))
                                              (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_te))
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_pair))
                                                        (Fan (Lift (KT K_oo))
                                                             (Lift (KT K_oo))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair K_ifLf
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                                  (ap2 Pair K_a2
                                    (ap2 Pair K_pair
                                      (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                                 (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo))))))))
                     r_ifLf
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_te))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (KT K_ifLf))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_te))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_te))
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_pair))
                                                 (Fan (Lift (KT K_oo))
                                                      (Lift (KT K_oo))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair K_te
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payA1 payA2)))
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payB1 payB2))))))
         (ap2 Pair K_a2
           (ap2 Pair K_ifLf
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA1 payB1)))
                        (ap2 Pair K_a2
                          (ap2 Pair K_pair
                            (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_te (ap2 Pair payA2 payB2)))
                                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair K_oo K_oo)))))))))
         lhsBuild rhsBuild

  thmTDispAxTreeEqNN_param : (a1T a2T b1T b2T : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axTreeEqNN
        (ap2 Pair a1T (ap2 Pair a2T (ap2 Pair b1T b2T)))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 TreeEq))
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair a1T a2T)))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair b1T b2T))))))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (reify (codeF2 IfLf))
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 TreeEq))
                  (ap2 Pair a1T b1T)))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 TreeEq))
                        (ap2 Pair a2T b2T)))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair O O))))))))))))
  thmTDispAxTreeEqNN_param a1T a2T b1T b2T =
    let payT = ap2 Pair a1T (ap2 Pair a2T (ap2 Pair b1T b2T))
        a    = ap2 Pair tagCode_axTreeEqNN payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeEqNN) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeEqNL payT
        s1   = skipAtTag (natCode tagAxI)        tagCode_axTreeEqNN payT b body_axI        next_axI
                  (teqDiff tagAxI        tagAxTreeEqNN refl)
        s2   = skipAtTag (natCode tagAxFst)      tagCode_axTreeEqNN payT b body_axFst      next_axFst
                  (teqDiff tagAxFst      tagAxTreeEqNN refl)
        s3   = skipAtTag (natCode tagAxSnd)      tagCode_axTreeEqNN payT b body_axSnd      next_axSnd
                  (teqDiff tagAxSnd      tagAxTreeEqNN refl)
        s4   = skipAtTag (natCode tagAxConst)    tagCode_axTreeEqNN payT b body_axConst    next_axConst
                  (teqDiff tagAxConst    tagAxTreeEqNN refl)
        s5   = skipAtTag (natCode tagAxComp)     tagCode_axTreeEqNN payT b body_axComp     next_axComp
                  (teqDiff tagAxComp     tagAxTreeEqNN refl)
        s6   = skipAtTag (natCode tagAxComp2)    tagCode_axTreeEqNN payT b body_axComp2    next_axComp2
                  (teqDiff tagAxComp2    tagAxTreeEqNN refl)
        s7   = skipAtTag (natCode tagAxLift)     tagCode_axTreeEqNN payT b body_axLift     next_axLift
                  (teqDiff tagAxLift     tagAxTreeEqNN refl)
        s8   = skipAtTag (natCode tagAxPost)     tagCode_axTreeEqNN payT b body_axPost     next_axPost
                  (teqDiff tagAxPost     tagAxTreeEqNN refl)
        s9   = skipAtTag (natCode tagAxFan)      tagCode_axTreeEqNN payT b body_axFan      next_axFan
                  (teqDiff tagAxFan      tagAxTreeEqNN refl)
        s10  = skipAtTag (natCode tagAxKT)       tagCode_axTreeEqNN payT b body_axZ       next_axKT
                  (teqDiff tagAxKT       tagAxTreeEqNN refl)
        s11  = skipAtTag (natCode tagAxRecLf)    tagCode_axTreeEqNN payT b body_axRecLf    next_axRecLf
                  (teqDiff tagAxRecLf    tagAxTreeEqNN refl)
        s12  = skipAtTag (natCode tagAxRecNd)    tagCode_axTreeEqNN payT b body_axRecNd    next_axRecNd
                  (teqDiff tagAxRecNd    tagAxTreeEqNN refl)
        s13  = skipAtTag (natCode tagAxRecPLf)   tagCode_axTreeEqNN payT b body_axRecPLf   next_axRecPLf
                  (teqDiff tagAxRecPLf   tagAxTreeEqNN refl)
        s14  = skipAtTag (natCode tagAxRecPNd)   tagCode_axTreeEqNN payT b body_axRecPNd   next_axRecPNd
                  (teqDiff tagAxRecPNd   tagAxTreeEqNN refl)
        s15  = skipAtTag (natCode tagAxIfLfL)    tagCode_axTreeEqNN payT b body_axIfLfL    next_axIfLfL
                  (teqDiff tagAxIfLfL    tagAxTreeEqNN refl)
        s16  = skipAtTag (natCode tagAxIfLfN)    tagCode_axTreeEqNN payT b body_axIfLfN    next_axIfLfN
                  (teqDiff tagAxIfLfN    tagAxTreeEqNN refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL) tagCode_axTreeEqNN payT b body_axTreeEqLL next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL tagAxTreeEqNN refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN) tagCode_axTreeEqNN payT b body_axTreeEqLN next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN tagAxTreeEqNN refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL) tagCode_axTreeEqNN payT b body_axTreeEqNL next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL tagAxTreeEqNN refl)
        hh   = hitAtTag  (natCode tagAxTreeEqNN) tagCode_axTreeEqNN payT b body_axTreeEqNN next_axTreeEqNN
                  (teqEq tagAxTreeEqNN)
        be   = body_axTreeEqNN_eval_param a1T a2T b1T b2T b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans s14 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans hh be))))))))))))))))))))

  ------------------------------------------------------------------
  -- Theorem 12 / Parts/Rec.agda parametric variant for axRecLf.
  -- Output is the explicit Pair structure with parametric zT, sT
  -- slots so that Parts/Rec.agda can use it for arbitrary z, s.

  body_axRecLf_eval_param : (zT sT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecLf (ap2 Pair tagCode_axRecLf (ap2 Pair zT sT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                              (ap2 Pair zT sT))
                    O))
        zT)))
  body_axRecLf_eval_param zT sT bb =
    let payZT  = zT
        payST  = sT
        payT   = ap2 Pair payZT payST
        a      = ap2 Pair tagCode_axRecLf payT
        K_a1V  = tagAp1
        K_a1   = reify K_a1V
        K_recV = leftT (codeF1 (Rec O IfLf))
        K_rec  = reify K_recV
        K_ooV  = lf
        K_oo   = reify K_ooV
        snd_a  = bodyLiftSndPair tagCode_axRecLf payT bb
        ext_z  = liftCompFstSnd_evalPair tagCode_axRecLf payZT payST bb
        kRecPayT = pairOfConst_eval K_recV (Lift Snd) a bb payT snd_a
        kOO    = liftKT_eval K_ooV a bb
        midLHS = pairOfFan_eval
                   (Fan (Lift (KT K_rec)) (Lift Snd) Pair)
                   (Lift (KT K_oo))
                   a bb
                   (ap2 Pair K_rec payT) K_oo
                   kRecPayT kOO
        lhsBuild = pairOfConst_eval K_a1V
                     (Fan (Fan (Lift (KT K_rec)) (Lift Snd) Pair)
                          (Lift (KT K_oo)) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rec payT) K_oo)
                     midLHS
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_rec)) (Lift Snd) Pair)
                   (Lift (KT K_oo)) Pair)
              Pair)
         (Lift (Comp Fst Snd)) a bb
         (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rec payT) K_oo)) payZT
         lhsBuild ext_z

  thmTDispAxRecLf_param : (zT sT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axRecLf (ap2 Pair zT sT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                              (ap2 Pair zT sT))
                    O))
        zT)))
  thmTDispAxRecLf_param zT sT =
    let payT = ap2 Pair zT sT
        a    = ap2 Pair tagCode_axRecLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecLf) (ap1 thmT payT)
        e1   = dispatchOpens tagAxKT payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecLf payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecLf refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecLf payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecLf refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecLf payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecLf refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecLf payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecLf refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecLf payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecLf refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecLf payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecLf refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecLf payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecLf refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecLf payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecLf refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecLf payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecLf refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecLf payT b body_axZ     next_axKT
                  (teqDiff tagAxKT     tagAxRecLf refl)
        hh   = hitAtTag  (natCode tagAxRecLf)  tagCode_axRecLf payT b body_axRecLf  next_axRecLf
                  (teqEq tagAxRecLf)
        be   = body_axRecLf_eval_param zT sT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans hh be)))))))))))

  ------------------------------------------------------------------
  -- Theorem 12 / Parts/RecP.agda parametric variant for axRecPLf.
  -- Output is the explicit Pair structure with parametric sT, pT
  -- slots so that Parts/RecP.agda can use it for arbitrary s, p.

  body_axRecPLf_eval_param : (sT pT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecPLf (ap2 Pair tagCode_axRecPLf (ap2 Pair sT pT)) bb)
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                    (ap2 Pair pT O)))
        O)))
  body_axRecPLf_eval_param sT pT bb =
    let payST  = sT
        payPT  = pT
        payT   = ap2 Pair payST payPT
        a      = ap2 Pair tagCode_axRecPLf payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_rPV  = leftT (codeF2 (RecP IfLf))
        K_rP   = reify K_rPV
        K_ooV  = lf
        K_oo   = reify K_ooV
        K_rhsV = lf
        K_rhs  = reify K_rhsV
        ext_s  = liftCompFstSnd_evalPair tagCode_axRecPLf payST payPT bb
        ext_p  = liftCompSndSnd_evalPair tagCode_axRecPLf payST payPT bb
        kOO    = liftKT_eval K_ooV a bb
        l_recPS = pairOfConst_eval K_rPV (Lift (Comp Fst Snd)) a bb payST ext_s
        l_pOO   = pairOfFan_eval (Lift (Comp Snd Snd)) (Lift (KT K_oo))
                    a bb payPT K_oo ext_p kOO
        l_inner = pairOfFan_eval
                    (Fan (Lift (KT K_rP)) (Lift (Comp Fst Snd)) Pair)
                    (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                    a bb
                    (ap2 Pair K_rP payST)
                    (ap2 Pair payPT K_oo)
                    l_recPS l_pOO
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_rP)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rP payST) (ap2 Pair payPT K_oo))
                     l_inner
        rhs = liftKT_eval K_rhsV a bb
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_rP)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Snd Snd)) (Lift (KT K_oo)) Pair) Pair)
              Pair)
         (Lift (KT K_rhs)) a bb
         (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rP payST)
                                    (ap2 Pair payPT K_oo)))
         K_rhs
         lhsBuild rhs

  thmTDispAxRecPLf_param : (sT pT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axRecPLf (ap2 Pair sT pT)))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                    (ap2 Pair pT O)))
        O)))
  thmTDispAxRecPLf_param sT pT =
    let payT = ap2 Pair sT pT
        a    = ap2 Pair tagCode_axRecPLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecPLf) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecNd payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecPLf payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecPLf refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecPLf payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecPLf refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecPLf payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecPLf refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecPLf payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecPLf refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecPLf payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecPLf refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecPLf payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecPLf refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecPLf payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecPLf refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecPLf payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecPLf refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecPLf payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecPLf refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecPLf payT b body_axZ     next_axKT
                  (teqDiff tagAxKT     tagAxRecPLf refl)
        s11  = skipAtTag (natCode tagAxRecLf)  tagCode_axRecPLf payT b body_axRecLf  next_axRecLf
                  (teqDiff tagAxRecLf  tagAxRecPLf refl)
        s12  = skipAtTag (natCode tagAxRecNd)  tagCode_axRecPLf payT b body_axRecNd  next_axRecNd
                  (teqDiff tagAxRecNd  tagAxRecPLf refl)
        hh   = hitAtTag  (natCode tagAxRecPLf) tagCode_axRecPLf payT b body_axRecPLf next_axRecPLf
                  (teqEq tagAxRecPLf)
        be   = body_axRecPLf_eval_param sT pT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans hh be)))))))))))))

  ------------------------------------------------------------------
  -- Theorem 12 / Parts/RecV2.agda parametric variant for axRecNd.
  -- Output is the explicit Pair structure with parametric zT, sT,
  -- aT, bT slots so that Parts/RecV2.agda can use it for arbitrary
  -- z, s, a, b at runtime via the recs slot of axRecNd.

  body_axRecNd_eval_param : (zT sT aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecNd
        (ap2 Pair tagCode_axRecNd (ap2 Pair zT (ap2 Pair sT (ap2 Pair aT bT)))) bb)
      (ap2 Pair
        -- LHS-encoded: code (ap1 (Rec z s) (ap2 Pair a b))
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                              (ap2 Pair zT sT))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair aT bT)))))
        -- RHS-encoded: code (ap2 s (ap2 Pair a b)
        --                          (ap2 Pair (ap1 (Rec z s) a) (ap1 (Rec z s) b)))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair sT
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT)))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                          (ap2 Pair zT sT))
                                aT))
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                          (ap2 Pair zT sT))
                                bT)))))))))))
  body_axRecNd_eval_param zT sT aT bT bb =
    let payZT  = zT
        payST  = sT
        payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payZT (ap2 Pair payST (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axRecNd payT
        K_a1V  = tagAp1
        K_a1   = reify K_a1V
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rTV  = leftT (codeF1 (Rec O IfLf))
        K_rT   = reify K_rTV
        ext_z  = liftCompFstSnd_evalPair tagCode_axRecNd payZT
                   (ap2 Pair payST (ap2 Pair payAT payBT)) bb
        ext_s  = liftFstSndSnd_evalPair3 tagCode_axRecNd payZT payST
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axRecNd payZT payST payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axRecNd payZT payST payAT payBT bb
        ----------------------------------------------------------------
        z_s_pair = pairOfFan_eval (Lift (Comp Fst Snd))
                     (Lift (Comp Fst (Comp Snd Snd))) a bb
                     payZT payST ext_z ext_s
        rec_zsst = pairOfConst_eval K_rTV
                     (Fan (Lift (Comp Fst Snd))
                          (Lift (Comp Fst (Comp Snd Snd))) Pair)
                     a bb (ap2 Pair payZT payST) z_s_pair
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        kPair_ab = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        sub1     = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) kPair_ab
        ----------------------------------------------------------------
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_rT))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                           Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_rT (ap2 Pair payZT payST))
                      (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                      rec_zsst sub1
        lhsBuild = pairOfConst_eval K_a1V
                     (Fan (Fan (Lift (KT K_rT))
                               (Fan (Lift (Comp Fst Snd))
                                    (Lift (Comp Fst (Comp Snd Snd))) Pair)
                               Pair)
                          (Fan (Lift (KT K_a2))
                               (Fan (Lift (KT K_pair))
                                    (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                         (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                         Pair) Pair) Pair)
                          Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST))
                       (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                     lhs_inner
        ----------------------------------------------------------------
        recA_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rT))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd))) Pair)
                            Pair)
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       a bb
                       (ap2 Pair K_rT (ap2 Pair payZT payST))
                       payAT
                       rec_zsst ext_a
        recA = pairOfConst_eval K_a1V
                 (Fan (Fan (Lift (KT K_rT))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                           Pair)
                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT)
                 recA_inner
        recB_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rT))
                            (Fan (Lift (Comp Fst Snd))
                                 (Lift (Comp Fst (Comp Snd Snd))) Pair)
                            Pair)
                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                       a bb
                       (ap2 Pair K_rT (ap2 Pair payZT payST))
                       payBT
                       rec_zsst ext_b
        recB = pairOfConst_eval K_a1V
                 (Fan (Fan (Lift (KT K_rT))
                           (Fan (Lift (Comp Fst Snd))
                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                           Pair)
                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)
                 recB_inner
        rec_AB = pairOfFan_eval
                   (Fan (Lift (KT K_a1))
                        (Fan (Fan (Lift (KT K_rT))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair)
                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                             Pair) Pair)
                   (Fan (Lift (KT K_a1))
                        (Fan (Fan (Lift (KT K_rT))
                                  (Fan (Lift (Comp Fst Snd))
                                       (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                  Pair)
                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                   (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))
                   recA recB
        sub2_kPair = pairOfConst_eval K_pairV
                       (Fan (Fan (Lift (KT K_a1))
                                 (Fan (Fan (Lift (KT K_rT))
                                           (Fan (Lift (Comp Fst Snd))
                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                           Pair)
                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      Pair) Pair)
                            (Fan (Lift (KT K_a1))
                                 (Fan (Fan (Lift (KT K_rT))
                                           (Fan (Lift (Comp Fst Snd))
                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                           Pair)
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                  (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)))
                       rec_AB
        sub2 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair))
                      (Fan (Fan (Lift (KT K_a1))
                                (Fan (Fan (Lift (KT K_rT))
                                          (Fan (Lift (Comp Fst Snd))
                                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                          Pair)
                                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair)
                           (Fan (Lift (KT K_a1))
                                (Fan (Fan (Lift (KT K_rT))
                                          (Fan (Lift (Comp Fst Snd))
                                               (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                          Pair)
                                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                              (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))))
                 sub2_kPair
        ----------------------------------------------------------------
        sub1_sub2 = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                     Pair) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Fan (Lift (KT K_a1))
                                          (Fan (Fan (Lift (KT K_rT))
                                                    (Fan (Lift (Comp Fst Snd))
                                                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                    Pair)
                                               (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                               Pair) Pair)
                                     (Fan (Lift (KT K_a1))
                                          (Fan (Fan (Lift (KT K_rT))
                                                    (Fan (Lift (Comp Fst Snd))
                                                         (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                    Pair)
                                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                               Pair) Pair)
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                      (ap2 Pair K_a2 (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                   (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)))))
                      sub1 sub2
        rhs_st_pair = pairOfFan_eval
                        (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                            Pair) Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Fan (Lift (KT K_a1))
                                                 (Fan (Fan (Lift (KT K_rT))
                                                           (Fan (Lift (Comp Fst Snd))
                                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                           Pair)
                                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                      Pair) Pair)
                                            (Fan (Lift (KT K_a1))
                                                 (Fan (Fan (Lift (KT K_rT))
                                                           (Fan (Lift (Comp Fst Snd))
                                                                (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                           Pair)
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair) Pair)
                                            Pair) Pair) Pair)
                             Pair)
                        a bb
                        payST
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair
                                     (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                                (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))))))
                        ext_s sub1_sub2
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a1))
                                                   (Fan (Fan (Lift (KT K_rT))
                                                             (Fan (Lift (Comp Fst Snd))
                                                                  (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                             Pair)
                                                        (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a1))
                                                   (Fan (Fan (Lift (KT K_rT))
                                                             (Fan (Lift (Comp Fst Snd))
                                                                  (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                             Pair)
                                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair payST
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair
                                    (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                               (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT)))))))
                     rhs_st_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a1))
              (Fan (Fan (Lift (KT K_rT))
                        (Fan (Lift (Comp Fst Snd))
                             (Lift (Comp Fst (Comp Snd Snd))) Pair)
                        Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Lift (KT K_pair))
                             (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair) Pair) Pair)
                   Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst (Comp Snd Snd)))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a1))
                                            (Fan (Fan (Lift (KT K_rT))
                                                      (Fan (Lift (Comp Fst Snd))
                                                           (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                      Pair)
                                                 (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a1))
                                            (Fan (Fan (Lift (KT K_rT))
                                                      (Fan (Lift (Comp Fst Snd))
                                                           (Lift (Comp Fst (Comp Snd Snd))) Pair)
                                                      Pair)
                                                 (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a1
           (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST))
             (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
         (ap2 Pair K_a2
           (ap2 Pair payST
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                        (ap2 Pair K_a2 (ap2 Pair K_pair
                          (ap2 Pair (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payAT))
                                     (ap2 Pair K_a1 (ap2 Pair (ap2 Pair K_rT (ap2 Pair payZT payST)) payBT))))))))
         lhsBuild rhsBuild

  thmTDispAxRecNd_param : (zT sT aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axRecNd
                   (ap2 Pair zT (ap2 Pair sT (ap2 Pair aT bT)))))
      (ap2 Pair
        (ap2 Pair (reify tagAp1)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                              (ap2 Pair zT sT))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair aT bT)))))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair sT
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT)))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                          (ap2 Pair zT sT))
                                aT))
                    (ap2 Pair (reify tagAp1)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF1 (Rec O IfLf))))
                                          (ap2 Pair zT sT))
                                bT)))))))))))
  thmTDispAxRecNd_param zT sT aT bT =
    let payT = ap2 Pair zT (ap2 Pair sT (ap2 Pair aT bT))
        a    = ap2 Pair tagCode_axRecNd payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecNd) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecLf payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecNd payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecNd refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecNd payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecNd refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecNd payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecNd refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecNd payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecNd refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecNd payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecNd refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecNd payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecNd refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecNd payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecNd refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecNd payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecNd refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecNd payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecNd refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecNd payT b body_axZ     next_axKT
                  (teqDiff tagAxKT     tagAxRecNd refl)
        s11  = skipAtTag (natCode tagAxRecLf)  tagCode_axRecNd payT b body_axRecLf  next_axRecLf
                  (teqDiff tagAxRecLf  tagAxRecNd refl)
        hh   = hitAtTag  (natCode tagAxRecNd)  tagCode_axRecNd payT b body_axRecNd  next_axRecNd
                  (teqEq tagAxRecNd)
        be   = body_axRecNd_eval_param zT sT aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans hh be))))))))))))

  ------------------------------------------------------------------
  -- Theorem 12 / Parts/RecP.agda parametric variant for axRecPNd.
  -- Term-form analog of body_axRecPNd_eval, taking sT, pT, aT, bT
  -- as Term parameters directly (without code/reify wrapping).

  body_axRecPNd_eval_param : (sT pT aT bT bb : Term) ->
    Deriv (atomic (eqn
      (ap2 body_axRecPNd
            (ap2 Pair tagCode_axRecPNd
              (ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT)))) bb)
      (ap2 Pair
        -- LHS: encoded (RecP s) p (Pair a b)
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
            (ap2 Pair pT
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT))))))
        -- RHS: encoded s (Pair p (Pair a b))(Pair (RecP s p a)(RecP s p b))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair sT
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair pT
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair aT bT))))))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                (ap2 Pair pT aT)))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                (ap2 Pair pT bT))))))))))))
  body_axRecPNd_eval_param sT pT aT bT bb =
    let payST  = sT
        payPT  = pT
        payAT  = aT
        payBT  = bT
        payT   = ap2 Pair payST (ap2 Pair payPT (ap2 Pair payAT payBT))
        a      = ap2 Pair tagCode_axRecPNd payT
        K_a2V  = tagAp2
        K_a2   = reify K_a2V
        K_pairV = codeF2 Pair
        K_pair = reify K_pairV
        K_rPTV = leftT (codeF2 (RecP IfLf))
        K_rPT  = reify K_rPTV
        ext_s  = liftCompFstSnd_evalPair tagCode_axRecPNd payST
                   (ap2 Pair payPT (ap2 Pair payAT payBT)) bb
        ext_p  = liftFstSndSnd_evalPair3 tagCode_axRecPNd payST payPT
                   (ap2 Pair payAT payBT) bb
        ext_a  = liftFstSndSndSnd_evalPair4 tagCode_axRecPNd payST payPT payAT payBT bb
        ext_b  = liftSndSndSndSnd_evalPair4 tagCode_axRecPNd payST payPT payAT payBT bb
        kRPT   = liftKT_eval K_rPTV a bb
        recP_st  = pairOfFan_eval (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) a bb
                     K_rPT payST kRPT ext_s
        ab_pair  = pairOfFan_eval
                     (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                     (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) a bb
                     payAT payBT ext_a ext_b
        kPair_ab = pairOfConst_eval K_pairV
                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                     a bb (ap2 Pair payAT payBT) ab_pair
        kA2_kPair_ab = pairOfConst_eval K_a2V
                     (Fan (Lift (KT K_pair))
                          (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                               (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                          Pair)
                     a bb (ap2 Pair K_pair (ap2 Pair payAT payBT)) kPair_ab
        lhs_pT_aPair = pairOfFan_eval
                         (Lift (Comp Fst (Comp Snd Snd)))
                         (Fan (Lift (KT K_a2))
                              (Fan (Lift (KT K_pair))
                                   (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                        (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                        Pair)
                                   Pair) Pair)
                         a bb
                         payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                         ext_p kA2_kPair_ab
        lhs_inner = pairOfFan_eval
                      (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           Pair)
                      a bb
                      (ap2 Pair K_rPT payST)
                      (ap2 Pair payPT
                        (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                      recP_st lhs_pT_aPair
        lhsBuild = pairOfConst_eval K_a2V
                     (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                          (Fan (Lift (Comp Fst (Comp Snd Snd)))
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                              (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                              Pair)
                                         Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair (ap2 Pair K_rPT payST)
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                     lhs_inner
        sub1_pPair = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd Snd)))
                       (Fan (Lift (KT K_a2))
                            (Fan (Lift (KT K_pair))
                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                      Pair)
                                 Pair) Pair)
                       a bb
                       payPT (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))
                       ext_p kA2_kPair_ab
        sub1_kPair = pairOfConst_eval K_pairV
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Fan (Lift (KT K_a2))
                                 (Fan (Lift (KT K_pair))
                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair payPT
                         (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))
                       sub1_pPair
        sub1 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair))
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Fan (Lift (KT K_a2))
                                (Fan (Lift (KT K_pair))
                                     (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair payPT
                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT)))))
                 sub1_kPair
        recA_pT_aT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                       a bb payPT payAT ext_p ext_a
        recA_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                       a bb
                       (ap2 Pair K_rPT payST)
                       (ap2 Pair payPT payAT)
                       recP_st recA_pT_aT
        recA = pairOfConst_eval K_a2V
                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Lift (Comp Fst (Comp Snd (Comp Snd Snd)))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT))
                 recA_inner
        recB_pT_bT = pairOfFan_eval
                       (Lift (Comp Fst (Comp Snd Snd)))
                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                       a bb payPT payBT ext_p ext_b
        recB_inner = pairOfFan_eval
                       (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                            (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                       a bb
                       (ap2 Pair K_rPT payST)
                       (ap2 Pair payPT payBT)
                       recP_st recB_pT_bT
        recB = pairOfConst_eval K_a2V
                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd)))) Pair)
                      Pair)
                 a bb
                 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))
                 recB_inner
        rec_AB = pairOfFan_eval
                   (Fan (Lift (KT K_a2))
                        (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                  Pair)
                             Pair) Pair)
                   (Fan (Lift (KT K_a2))
                        (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                             (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                  (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                  Pair)
                             Pair) Pair)
                   a bb
                   (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                   (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))
                   recA recB
        sub2_kPair = pairOfConst_eval K_pairV
                       (Fan (Fan (Lift (KT K_a2))
                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                           (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            (Fan (Lift (KT K_a2))
                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                           Pair)
                                      Pair) Pair)
                            Pair)
                       a bb
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                  (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))))
                       rec_AB
        sub2 = pairOfConst_eval K_a2V
                 (Fan (Lift (KT K_pair))
                      (Fan (Fan (Lift (KT K_a2))
                                (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                          (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           (Fan (Lift (KT K_a2))
                                (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                     (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                          (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                          Pair)
                                     Pair) Pair)
                           Pair) Pair)
                 a bb
                 (ap2 Pair K_pair
                   (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                              (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))))
                 sub2_kPair
        sub1_sub2 = pairOfFan_eval
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                     (Fan (Lift (KT K_a2))
                                          (Fan (Lift (KT K_pair))
                                               (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                    Pair)
                                               Pair) Pair)
                                     Pair) Pair) Pair)
                      (Fan (Lift (KT K_a2))
                           (Fan (Lift (KT K_pair))
                                (Fan (Fan (Lift (KT K_a2))
                                          (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                    (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                    Pair)
                                               Pair) Pair)
                                     (Fan (Lift (KT K_a2))
                                          (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                               (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                    (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                    Pair)
                                               Pair) Pair)
                                     Pair) Pair) Pair)
                      a bb
                      (ap2 Pair K_a2 (ap2 Pair K_pair
                        (ap2 Pair payPT
                          (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                      (ap2 Pair K_a2 (ap2 Pair K_pair
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                   (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))))))
                      sub1 sub2
        rhs_st_pair = pairOfFan_eval
                        (Lift (Comp Fst Snd))
                        (Fan (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                            (Fan (Lift (KT K_a2))
                                                 (Fan (Lift (KT K_pair))
                                                      (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                           Pair)
                                                      Pair) Pair)
                                            Pair) Pair) Pair)
                             (Fan (Lift (KT K_a2))
                                  (Fan (Lift (KT K_pair))
                                       (Fan (Fan (Lift (KT K_a2))
                                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                           (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                           Pair)
                                                      Pair) Pair)
                                            (Fan (Lift (KT K_a2))
                                                 (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                      (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                           (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                           Pair)
                                                      Pair) Pair)
                                            Pair) Pair) Pair)
                             Pair)
                        a bb
                        payST
                        (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair
                                    (ap2 Pair payPT
                                      (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                                   (ap2 Pair K_a2 (ap2 Pair K_pair
                                     (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                                (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))))))
                        ext_s sub1_sub2
        rhsBuild = pairOfConst_eval K_a2V
                     (Fan (Lift (Comp Fst Snd))
                          (Fan (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Lift (KT K_pair))
                                                        (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               (Fan (Lift (KT K_a2))
                                    (Fan (Lift (KT K_pair))
                                         (Fan (Fan (Lift (KT K_a2))
                                                   (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              (Fan (Lift (KT K_a2))
                                                   (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                        (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                             (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                             Pair)
                                                        Pair) Pair)
                                              Pair) Pair) Pair)
                               Pair) Pair)
                     a bb
                     (ap2 Pair payST
                       (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair
                                   (ap2 Pair payPT
                                     (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                                  (ap2 Pair K_a2 (ap2 Pair K_pair
                                    (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                               (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT))))))))
                     rhs_st_pair
    in pairOfFan_eval
         (Fan (Lift (KT K_a2))
              (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                   (Fan (Lift (Comp Fst (Comp Snd Snd)))
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                       (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                       Pair)
                                  Pair) Pair)
                        Pair) Pair) Pair)
         (Fan (Lift (KT K_a2))
              (Fan (Lift (Comp Fst Snd))
                   (Fan (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Lift (KT K_pair))
                                                 (Fan (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        (Fan (Lift (KT K_a2))
                             (Fan (Lift (KT K_pair))
                                  (Fan (Fan (Lift (KT K_a2))
                                            (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Fst (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       (Fan (Lift (KT K_a2))
                                            (Fan (Fan (Lift (KT K_rPT)) (Lift (Comp Fst Snd)) Pair)
                                                 (Fan (Lift (Comp Fst (Comp Snd Snd)))
                                                      (Lift (Comp Snd (Comp Snd (Comp Snd Snd))))
                                                      Pair)
                                                 Pair) Pair)
                                       Pair) Pair) Pair)
                        Pair) Pair) Pair)
         a bb
         (ap2 Pair K_a2
           (ap2 Pair (ap2 Pair K_rPT payST)
             (ap2 Pair payPT
               (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
         (ap2 Pair K_a2
           (ap2 Pair payST
             (ap2 Pair (ap2 Pair K_a2 (ap2 Pair K_pair
                         (ap2 Pair payPT
                           (ap2 Pair K_a2 (ap2 Pair K_pair (ap2 Pair payAT payBT))))))
                        (ap2 Pair K_a2 (ap2 Pair K_pair
                          (ap2 Pair (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payAT)))
                                     (ap2 Pair K_a2 (ap2 Pair (ap2 Pair K_rPT payST) (ap2 Pair payPT payBT)))))))))
         lhsBuild rhsBuild

  thmTDispAxRecPNd_param : (sT pT aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axRecPNd
                   (ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT)))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
            (ap2 Pair pT
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair aT bT))))))
        (ap2 Pair (reify tagAp2)
          (ap2 Pair sT
            (ap2 Pair
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair pT
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (reify (codeF2 Pair))
                        (ap2 Pair aT bT))))))
              (ap2 Pair (reify tagAp2)
                (ap2 Pair (reify (codeF2 Pair))
                  (ap2 Pair
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                (ap2 Pair pT aT)))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (RecP IfLf)))) sT)
                                (ap2 Pair pT bT))))))))))))
  thmTDispAxRecPNd_param sT pT aT bT =
    let payT = ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT))
        a    = ap2 Pair tagCode_axRecPNd payT
        b    = ap2 Pair (ap1 thmT tagCode_axRecPNd) (ap1 thmT payT)
        e1   = dispatchOpens tagAxRecPLf payT
        s1   = skipAtTag (natCode tagAxI)      tagCode_axRecPNd payT b body_axI      next_axI
                  (teqDiff tagAxI      tagAxRecPNd refl)
        s2   = skipAtTag (natCode tagAxFst)    tagCode_axRecPNd payT b body_axFst    next_axFst
                  (teqDiff tagAxFst    tagAxRecPNd refl)
        s3   = skipAtTag (natCode tagAxSnd)    tagCode_axRecPNd payT b body_axSnd    next_axSnd
                  (teqDiff tagAxSnd    tagAxRecPNd refl)
        s4   = skipAtTag (natCode tagAxConst)  tagCode_axRecPNd payT b body_axConst  next_axConst
                  (teqDiff tagAxConst  tagAxRecPNd refl)
        s5   = skipAtTag (natCode tagAxComp)   tagCode_axRecPNd payT b body_axComp   next_axComp
                  (teqDiff tagAxComp   tagAxRecPNd refl)
        s6   = skipAtTag (natCode tagAxComp2)  tagCode_axRecPNd payT b body_axComp2  next_axComp2
                  (teqDiff tagAxComp2  tagAxRecPNd refl)
        s7   = skipAtTag (natCode tagAxLift)   tagCode_axRecPNd payT b body_axLift   next_axLift
                  (teqDiff tagAxLift   tagAxRecPNd refl)
        s8   = skipAtTag (natCode tagAxPost)   tagCode_axRecPNd payT b body_axPost   next_axPost
                  (teqDiff tagAxPost   tagAxRecPNd refl)
        s9   = skipAtTag (natCode tagAxFan)    tagCode_axRecPNd payT b body_axFan    next_axFan
                  (teqDiff tagAxFan    tagAxRecPNd refl)
        s10  = skipAtTag (natCode tagAxKT)     tagCode_axRecPNd payT b body_axZ      next_axKT
                  (teqDiff tagAxKT     tagAxRecPNd refl)
        s11  = skipAtTag (natCode tagAxRecLf)  tagCode_axRecPNd payT b body_axRecLf  next_axRecLf
                  (teqDiff tagAxRecLf  tagAxRecPNd refl)
        s12  = skipAtTag (natCode tagAxRecNd)  tagCode_axRecPNd payT b body_axRecNd  next_axRecNd
                  (teqDiff tagAxRecNd  tagAxRecPNd refl)
        s13  = skipAtTag (natCode tagAxRecPLf) tagCode_axRecPNd payT b body_axRecPLf next_axRecPLf
                  (teqDiff tagAxRecPLf tagAxRecPNd refl)
        hh   = hitAtTag  (natCode tagAxRecPNd) tagCode_axRecPNd payT b body_axRecPNd next_axRecPNd
                  (teqEq tagAxRecPNd)
        be   = body_axRecPNd_eval_param sT pT aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s11
       (ruleTrans s12 (ruleTrans s13 (ruleTrans hh be))))))))))))))

------------------------------------------------------------------------
-- WithDispatch : module parameterised by the 30 dispatch lemmas not
-- proved in this session.  Sessions D-F instantiate.
--
-- 21 non-recursive (axiomatic):
--   axRecLf  axRecNd  axRecPLf  axRecPNd
--   axIfLfL  axIfLfN
--   axTreeEqLL  axTreeEqLN  axTreeEqNL  axTreeEqNN  axGoodstein
--   axRefl
--   axEqTrans  axEqCong1  axEqCongL  axEqCongR
--   axK  axS  axNeg  axExFalso  axContrapos
--
-- 8 recursive (sub-proof bearing):
--   ruleSym  ruleTrans  cong1  congL  congR  ruleInst
--   mp  ruleIndBT
--
-- Recursive signatures parametric over an abstract conclusion  Q1 ,
-- per the StepProto.agda  mp_dispatch_sub  template:  given a
-- sub-proof hypothesis on  thmT(reify y_first) , conclude the same
-- conclusion for  thmT(reify (encX ... y_first ...)) .  Sub-proof
-- trees that need the inner-pair passthrough (mp, ruleTrans,
-- ruleIndBT) carry the  nd (nd y_aL y_aR) y_ar  shape.

module WithDispatch
  ------------------------------------------------------------------
  -- 21 non-recursive deferred dispatches.  Each produces  reify(outX)
  -- (= reify of the corresponding  codeFormula  of the conclusion),
  -- matching what the encoder needs to be one-line per case.


  ------------------------------------------------------------------
  -- 9 recursive deferred dispatches.  Each takes sub-proof
  -- derivations whose RHSs are  reify(codeFormula <sub-conclusion>)
  -- and produces  reify(outX) = reify(codeFormula <conclusion>) .

  where

  ------------------------------------------------------------------
  -- The encoder, in two flavours.
  --
  --  * encodeRich  pattern-matches on  Deriv P  with one case per
  --    primitive and returns a 4-deep Sigma carrying:
  --       (i)  the encoding tree  y ;
  --       (ii) a head-rest term  y'  such that  Fst (reify y) = Pair O y' ;
  --       (iii) a Deriv proof of (ii);
  --       (iv) the dispatch Deriv  thmT (reify y) = reify (codeFormula P) .
  --    The shape proof (iii) lets recursive primitives whose payloads
  --    are inner-pair (mp, ruleTrans) discharge the
  --    inner-pair-passthrough lemma without needing case analysis on
  --    sub-proof structure.
  --
  --  * encode  is a 1-line projection of  encodeRich  with the simpler
  --    ( y , dispatch )  Sigma return type expected by  BRA.Thm11.Thm11 .
  --
  -- mkR  bundles a known-tag encoding  y = nd (natCode (suc m)) rest
  -- (and its dispatch derivation) into the rich return type.  All
  --  encX  functions return exactly this shape, so each case is
  -- one-line:  mkR P m rest (thmTDispX ...) .

  mkR : (P : Formula) (m : Nat) (rest : Tree) ->
    Deriv (atomic (eqn (ap1 thmT (reify (nd (natCode (suc m)) rest)))
                       (reify (codeFormula P)))) ->
    Sigma Tree (\ y ->
      Sigma Term (\ y' ->
        Sigma (Deriv (atomic (eqn (ap1 Fst (reify y)) (ap2 Pair O y'))))
              (\ _ -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                          (reify (codeFormula P)))))))
  mkR P m rest d =
    mkSigma (nd (natCode (suc m)) rest)
      (mkSigma (reify (natCode m))
        (mkSigma (axFst (reify (natCode (suc m))) (reify rest)) d))

  encodeRich : (P : Formula) -> Deriv P ->
    Sigma Tree (\ y ->
      Sigma Term (\ y' ->
        Sigma (Deriv (atomic (eqn (ap1 Fst (reify y)) (ap2 Pair O y'))))
              (\ _ -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                          (reify (codeFormula P)))))))

  -- Group I (10 axiom cases, all concrete dispatches).
  encodeRich .(atomic (eqn (ap1 I t) t)) (axI t) =
    mkR (atomic (eqn (ap1 I t) t)) zero (code t) (thmTDispAxI t)
  encodeRich .(atomic (eqn (ap1 Fst (ap2 Pair a' b')) a')) (axFst a' b') =
    mkR (atomic (eqn (ap1 Fst (ap2 Pair a' b')) a')) tagAxI
        (nd (code a') (code b')) (thmTDispAxFst a' b')
  encodeRich .(atomic (eqn (ap1 Snd (ap2 Pair a' b')) b')) (axSnd a' b') =
    mkR (atomic (eqn (ap1 Snd (ap2 Pair a' b')) b')) tagAxFst
        (nd (code a') (code b')) (thmTDispAxSnd a' b')
  encodeRich .(atomic (eqn (ap2 Const a' b') a')) (axConst a' b') =
    mkR (atomic (eqn (ap2 Const a' b') a')) tagAxSnd
        (nd (code a') (code b')) (thmTDispAxConst a' b')
  encodeRich .(atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))) (axComp f g t) =
    mkR (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))) tagAxConst
        (nd (codeF1 f) (nd (codeF1 g) (code t))) (thmTDispAxComp f g t)
  encodeRich .(atomic (eqn (ap1 (Comp2 h' f g) t) (ap2 h' (ap1 f t) (ap1 g t))))
             (axComp2 h' f g t) =
    mkR (atomic (eqn (ap1 (Comp2 h' f g) t) (ap2 h' (ap1 f t) (ap1 g t))))
        tagAxComp
        (nd (codeF2 h') (nd (codeF1 f) (nd (codeF1 g) (code t))))
        (thmTDispAxComp2 h' f g t)
  encodeRich .(atomic (eqn (ap2 (Lift f) a' b') (ap1 f a'))) (axLift f a' b') =
    mkR (atomic (eqn (ap2 (Lift f) a' b') (ap1 f a'))) tagAxComp2
        (nd (codeF1 f) (nd (code a') (code b'))) (thmTDispAxLift f a' b')
  encodeRich .(atomic (eqn (ap2 (Post f h') a' b') (ap1 f (ap2 h' a' b'))))
             (axPost f h' a' b') =
    mkR (atomic (eqn (ap2 (Post f h') a' b') (ap1 f (ap2 h' a' b'))))
        tagAxLift
        (nd (codeF1 f) (nd (codeF2 h') (nd (code a') (code b'))))
        (thmTDispAxPost f h' a' b')
  encodeRich .(atomic (eqn (ap2 (Fan h1 h2 h') a' b')
                            (ap2 h' (ap2 h1 a' b') (ap2 h2 a' b'))))
             (axFan h1 h2 h' a' b') =
    mkR (atomic (eqn (ap2 (Fan h1 h2 h') a' b')
                      (ap2 h' (ap2 h1 a' b') (ap2 h2 a' b'))))
        tagAxPost
        (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h') (nd (code a') (code b')))))
        (thmTDispAxFan h1 h2 h' a' b')
  encodeRich .(atomic (eqn (ap1 Z x) O)) (axZ x) =
    mkR (atomic (eqn (ap1 Z x) O)) tagAxFan
        (nd (codeF1 Z) (code x)) (thmTDispAxZ x)

  -- Group II (deferred non-recursive: 11 cases, axRecLf..axGoodstein).
  encodeRich .(atomic (eqn (ap1 (Rec z s) O) z)) (axRecLf z s) =
    mkR (atomic (eqn (ap1 (Rec z s) O) z)) tagAxKT
        (nd (code z) (codeF2 s)) (thmTDispAxRecLf z s)
  encodeRich .(atomic (eqn (ap1 (Rec z s) (ap2 Pair a' b'))
                            (ap2 s (ap2 Pair a' b')
                                   (ap2 Pair (ap1 (Rec z s) a') (ap1 (Rec z s) b')))))
             (axRecNd z s a' b') =
    mkR (atomic (eqn (ap1 (Rec z s) (ap2 Pair a' b'))
                      (ap2 s (ap2 Pair a' b')
                             (ap2 Pair (ap1 (Rec z s) a') (ap1 (Rec z s) b')))))
        tagAxRecLf
        (nd (code z) (nd (codeF2 s) (nd (code a') (code b'))))
        (thmTDispAxRecNd z s a' b')
  encodeRich .(atomic (eqn (ap2 (RecP s) p O) O)) (axRecPLf s p) =
    mkR (atomic (eqn (ap2 (RecP s) p O) O)) tagAxRecNd
        (nd (codeF2 s) (code p)) (thmTDispAxRecPLf s p)
  encodeRich .(atomic (eqn (ap2 (RecP s) p (ap2 Pair a' b'))
                            (ap2 s (ap2 Pair p (ap2 Pair a' b'))
                                   (ap2 Pair (ap2 (RecP s) p a') (ap2 (RecP s) p b')))))
             (axRecPNd s p a' b') =
    mkR (atomic (eqn (ap2 (RecP s) p (ap2 Pair a' b'))
                      (ap2 s (ap2 Pair p (ap2 Pair a' b'))
                             (ap2 Pair (ap2 (RecP s) p a') (ap2 (RecP s) p b')))))
        tagAxRecPLf
        (nd (codeF2 s) (nd (code p) (nd (code a') (code b'))))
        (thmTDispAxRecPNd s p a' b')
  encodeRich .(atomic (eqn (ap2 IfLf O (ap2 Pair a' b')) a')) (axIfLfL a' b') =
    mkR (atomic (eqn (ap2 IfLf O (ap2 Pair a' b')) a')) tagAxRecPNd
        (nd (code a') (code b')) (thmTDispAxIfLfL a' b')
  encodeRich .(atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a' b')) b'))
             (axIfLfN x y a' b') =
    mkR (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a' b')) b'))
        tagAxIfLfL
        (nd (code x) (nd (code y) (nd (code a') (code b'))))
        (thmTDispAxIfLfN x y a' b')
  encodeRich .(atomic (eqn (ap2 TreeEq O O) O)) axTreeEqLL =
    mkR (atomic (eqn (ap2 TreeEq O O) O)) tagAxIfLfN lf thmTDispAxTreeEqLL
  encodeRich .(atomic (eqn (ap2 TreeEq O (ap2 Pair a' b')) (ap2 Pair O O)))
             (axTreeEqLN a' b') =
    mkR (atomic (eqn (ap2 TreeEq O (ap2 Pair a' b')) (ap2 Pair O O)))
        tagAxTreeEqLL
        (nd (code a') (code b')) (thmTDispAxTreeEqLN a' b')
  encodeRich .(atomic (eqn (ap2 TreeEq (ap2 Pair a' b') O) (ap2 Pair O O)))
             (axTreeEqNL a' b') =
    mkR (atomic (eqn (ap2 TreeEq (ap2 Pair a' b') O) (ap2 Pair O O)))
        tagAxTreeEqLN
        (nd (code a') (code b')) (thmTDispAxTreeEqNL a' b')
  encodeRich .(atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                            (ap2 IfLf (ap2 TreeEq a1 b1)
                                      (ap2 Pair (ap2 TreeEq a2 b2)
                                                (ap2 Pair O O)))))
             (axTreeEqNN a1 a2 b1 b2) =
    mkR (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                      (ap2 IfLf (ap2 TreeEq a1 b1)
                                (ap2 Pair (ap2 TreeEq a2 b2)
                                          (ap2 Pair O O)))))
        tagAxTreeEqNL
        (nd (code a1) (nd (code a2) (nd (code b1) (code b2))))
        (thmTDispAxTreeEqNN a1 a2 b1 b2)
  encodeRich .(atomic (eqn (ap2 IfLf (ap2 TreeEq a' b') (ap2 Pair a' O))
                            (ap2 IfLf (ap2 TreeEq a' b') (ap2 Pair b' O))))
             (axGoodstein a' b') =
    mkR (atomic (eqn (ap2 IfLf (ap2 TreeEq a' b') (ap2 Pair a' O))
                      (ap2 IfLf (ap2 TreeEq a' b') (ap2 Pair b' O))))
        tagAxTreeEqNN
        (nd (code a') (code b')) (thmTDispAxGoodstein a' b')

  -- Group III (axRefl + 5 recursive).  axRefl, ruleSym are concrete;
  -- ruleTrans is concrete (uses head-shape from r1); cong1, congL,
  -- congR remain deferred.
  encodeRich .(atomic (eqn t t)) (axRefl t) =
    mkR (atomic (eqn t t)) tagAxGoodstein (code t) (thmTDispAxRefl t)
  encodeRich .(atomic (eqn u t)) (ruleSym {t = t} {u = u} pf) =
    let rec = encodeRich (atomic (eqn t u)) pf
        y_h = fst rec
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn u t)) tagAxRefl y_h
           (thmTDispRuleSym t u y_h d_h)
  encodeRich .(atomic (eqn t v)) (ruleTrans {t = t} {u = u} {v = v} pf1 pf2) =
    let r1 = encodeRich (atomic (eqn t u)) pf1
        r2 = encodeRich (atomic (eqn u v)) pf2
        y1 = fst r1
        y1' = fst (snd r1)
        shape1 = fst (snd (snd r1))
        d1 = snd (snd (snd r1))
        y2 = fst r2
        d2 = snd (snd (snd r2))
    in mkR (atomic (eqn t v)) tagRuleSym (nd y1 y2)
           (thmTDispRuleTrans t u v y1 y2 y1' shape1 d1 d2)
  encodeRich .(atomic (eqn (ap1 f t) (ap1 f u))) (cong1 f {t = t} {u = u} pf) =
    let rec = encodeRich (atomic (eqn t u)) pf
        y_h = fst rec
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn (ap1 f t) (ap1 f u))) tagRuleTrans
           (nd (codeF1 f) y_h)
           (thmTDispCong1 f t u y_h d_h)
  encodeRich .(atomic (eqn (ap2 g t x) (ap2 g u x)))
             (congL g {t = t} {u = u} x pf) =
    let rec = encodeRich (atomic (eqn t u)) pf
        y_h = fst rec
        y_h' = fst (snd rec)
        shape_h = fst (snd (snd rec))
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn (ap2 g t x) (ap2 g u x))) tagCong1
           (nd (codeF2 g) (nd y_h (code x)))
           (thmTDispCongL g x t u y_h y_h' shape_h d_h)
  encodeRich .(atomic (eqn (ap2 g x t) (ap2 g x u)))
             (congR g x {t = t} {u = u} pf) =
    let rec = encodeRich (atomic (eqn t u)) pf
        y_h = fst rec
        y_h' = fst (snd rec)
        shape_h = fst (snd (snd rec))
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn (ap2 g x t) (ap2 g x u))) tagCongL
           (nd (codeF2 g) (nd y_h (code x)))
           (thmTDispCongR g x t u y_h y_h' shape_h d_h)

  -- Group IV (deferred non-recursive: axEqTrans..axContrapos).
  encodeRich .((atomic (eqn a' b'))
                imp ((atomic (eqn a' c'))
                      imp (atomic (eqn b' c'))))
             (axEqTrans a' b' c') =
    mkR ((atomic (eqn a' b'))
          imp ((atomic (eqn a' c'))
                imp (atomic (eqn b' c'))))
        tagCongR
        (nd (code a') (nd (code b') (code c')))
        (thmTDispAxEqTrans a' b' c')
  encodeRich .((atomic (eqn a' b'))
                imp (atomic (eqn (ap1 f a') (ap1 f b'))))
             (axEqCong1 f a' b') =
    mkR ((atomic (eqn a' b'))
          imp (atomic (eqn (ap1 f a') (ap1 f b'))))
        tagAxEqTrans
        (nd (codeF1 f) (nd (code a') (code b')))
        (thmTDispAxEqCong1 f a' b')
  encodeRich .((atomic (eqn a' b'))
                imp (atomic (eqn (ap2 g a' c') (ap2 g b' c'))))
             (axEqCongL g a' b' c') =
    mkR ((atomic (eqn a' b'))
          imp (atomic (eqn (ap2 g a' c') (ap2 g b' c'))))
        tagAxEqCong1
        (nd (codeF2 g) (nd (code a') (nd (code b') (code c'))))
        (thmTDispAxEqCongL g a' b' c')
  encodeRich .((atomic (eqn a' b'))
                imp (atomic (eqn (ap2 g c' a') (ap2 g c' b'))))
             (axEqCongR g a' b' c') =
    mkR ((atomic (eqn a' b'))
          imp (atomic (eqn (ap2 g c' a') (ap2 g c' b'))))
        tagAxEqCongL
        (nd (codeF2 g) (nd (code a') (nd (code b') (code c'))))
        (thmTDispAxEqCongR g a' b' c')
  encodeRich .(P imp (Q imp P)) (axK P Q) =
    mkR (P imp (Q imp P)) tagAxEqCongR
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxK P Q)
  encodeRich .((P imp (Q imp R)) imp ((P imp Q) imp (P imp R))) (axS P Q R) =
    mkR ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R))) tagAxK
        (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R)))
        (thmTDispAxS P Q R)
  encodeRich .((not P) imp ((not Q) imp (Q imp P))) (axNeg P Q) =
    mkR ((not P) imp ((not Q) imp (Q imp P))) tagAxS
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxNeg P Q)
  encodeRich .(P imp ((not P) imp Q)) (axExFalso P Q) =
    mkR (P imp ((not P) imp Q)) tagAxNeg
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxExFalso P Q)
  encodeRich .((P imp Q) imp ((not Q) imp (not P))) (axContrapos P Q) =
    mkR ((P imp Q) imp ((not Q) imp (not P))) tagAxExFalso
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxContrapos P Q)

  -- Group V (mp + ruleInst + ruleIndBT; mp is concrete using
  -- shape from r1, ruleIndBT is concrete, ruleInst is deferred).
  encodeRich Q (mp {P = P} pf1 pf2) =
    let r1 = encodeRich (P imp Q) pf1
        r2 = encodeRich P pf2
        y1 = fst r1
        y1' = fst (snd r1)
        shape1 = fst (snd (snd r1))
        d1 = snd (snd (snd r1))
        y2 = fst r2
        d2 = snd (snd (snd r2))
    in mkR Q tagAxContrapos (nd y1 y2)
           (thmTDispMp P Q y1 y2 y1' shape1 d1 d2)
  encodeRich .(substF x t P) (ruleInst x t {P = P} pf) =
    let rec = encodeRich P pf
        y_h = fst rec
        y_h' = fst (snd rec)
        shape_h = fst (snd (snd rec))
        d_h = snd (snd (snd rec))
    in mkR (substF x t P) tagMp
           (nd (code (var x)) (nd y_h (code t)))
           (thmTDispRuleInst x t P y_h y_h' shape_h d_h)
  encodeRich P (ruleIndBT .P v1 v2 pf_base pf_step) =
    let r1 = encodeRich (substF zero O P) pf_base
        r2 = encodeRich ((substF zero (var v1) P) imp
                           ((substF zero (var v2) P) imp
                            (substF zero (ap2 Pair (var v1) (var v2)) P))) pf_step
        y_b = fst r1
        y_s = fst r2
        d_b = snd (snd (snd r1))
        d_s = snd (snd (snd r2))
    in mkR P tagRuleInst
           (nd (codeFormula P) (nd (code (var v1)) (nd (code (var v2)) (nd y_b y_s))))
           (thmTDispRuleIndBT P v1 v2 y_b y_s d_b d_s)
  -- Group III (4 safe-default axioms).
  encodeRich .(atomic (eqn (ap1 Fst O) O)) axFstLf =
    mkR (atomic (eqn (ap1 Fst O) O)) tagRuleIndBT lf thmTDispAxFstLf
  encodeRich .(atomic (eqn (ap1 Snd O) O)) axSndLf =
    mkR (atomic (eqn (ap1 Snd O) O)) tagAxFstLf lf thmTDispAxSndLf
  encodeRich .(atomic (eqn (ap2 IfLf O O) O)) axIfLfLL =
    mkR (atomic (eqn (ap2 IfLf O O) O)) tagAxSndLf lf thmTDispAxIfLfLL
  encodeRich .(atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O)) (axIfLfNL x y) =
    mkR (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O)) tagAxIfLfLL
        (nd (code x) (code y)) (thmTDispAxIfLfNL x y)
  -- Lite projection for  BRA.Thm11.Thm11 .
  encode : (P : Formula) -> Deriv P ->
           Sigma Tree (\ y ->
             Deriv (atomic (eqn (ap1 thmT (reify y))
                                 (reify (codeFormula P)))))
  encode P pf =
    let r = encodeRich P pf
    in mkSigma (fst r) (snd (snd (snd r)))

  ------------------------------------------------------------------
  -- Theorem 11 / Goedel I (parameterised by the 30 deferred
  -- dispatches).  Once Sessions D-F deliver them, this re-export
  -- becomes  thm11 : Deriv G -> Deriv (atomic (eqn trueT falseT)) .

  open import BRA.Thm11 using (module Thm11)
  open Thm11 thmT thClosed codeF1Th_noVar encode public
    using (thm11-exported)

  -- Headline theorem.  G is the Goedel sentence (constructed by the
  -- Diagonal module from the spec  thmT, thClosed, codeF1Th_noVar ).
  -- This re-export is itself parametric over the 30 deferred dispatch
  -- lemmas; once Sessions D-F deliver them, instantiating WithDispatch
  -- yields  thm11  unconditional.
  thm11 = thm11-exported
