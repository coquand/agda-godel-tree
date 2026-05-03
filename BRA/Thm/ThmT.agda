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
--   thmT      = Rec stepProtoWrapped
--   stepProtoWrapped = Fan (Lift Snd) (Post Snd Pair) stepProto
--     -- absorbs the  Pair O ...  wrapper introduced by  Rec  (now an
--     -- Agda function over  treeRec ); see  dispatchOpens  for proof.
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
open import BRA.SbParam using (codedSubstT)
open import BRA.CodeCommutes using (codeCommutesFormula)
open import BRA.SoundMpProto using (body_mp_v)
open import BRA.SoundMpVProof using (body_mp_v_eval_pass ; body_mp_v_eval_pass_l)
open import BRA.SoundRuleInstProto using (body_ruleInst_v)
open import BRA.SoundRuleInstVProof using (body_ruleInst_v_eval_pass ; body_ruleInst_v_eval_pass_l ; codeFormulaPairShape)
open import BRA.SoundRuleSymProto using (body_ruleSym_v)
open import BRA.SoundRuleSymVProof using (body_ruleSym_v_eval_pass ; body_ruleSym_v_eval_pass_l)
open import BRA.SoundCong1Proto using (body_cong1_v)
open import BRA.SoundCong1VProof using (body_cong1_v_eval_pass)
open import BRA.SoundCongLProto using (body_congL_v)
open import BRA.SoundCongLVProof using
  ( body_congL_v_eval_pass ; body_congL_v_eval_pass_l ; body_congL_v_eval_pass_dl )
open import BRA.SoundCongRProto using (body_congR_v)
open import BRA.SoundCongRVProof using
  ( body_congR_v_eval_pass ; body_congR_v_eval_pass_l ; body_congR_v_eval_pass_dl )
open import BRA.SoundRuleTransProto using (body_ruleTrans_v)
open import BRA.SoundRuleTransVProof using
  ( body_ruleTrans_v_eval_pass ; body_ruleTrans_v_eval_pass_l
  ; body_ruleTrans_v_eval_pass_dl )
open import BRA.SoundRuleInst2Proto using ( body_ruleInst2_v )
open import BRA.SoundRuleInst2Proto as RI2Proto using ()
open import BRA.SoundRuleInst2VProof using ( body_ruleInst2_v_eval_pass )
open import BRA.SoundRuleIndBTProto using ( body_ruleIndBT_v )
open import BRA.SoundRuleIndBTVProof using ( body_ruleIndBT_v_eval_pass )
open import BRA.TreeEqReflParam using (treeEqReflParam)
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
-- AxRecLf / AxRecNd Parts deleted: axRecLf and axRecNd demoted to
-- derived top-level lemmas in BRA.Deriv (see refactor 2026-05-01).
open import BRA.Thm.Parts.AxTreeRecLf
open import BRA.Thm.Parts.AxTreeRecNd
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
-- Reified tag-code constants extracted to BRA.Thm.TagCodes so that
-- per-axiom Parts/Ax*.agda files can name them without going through
-- this file.

open import BRA.Thm.TagCodes public

------------------------------------------------------------------------
-- Lift / position-extractor helpers extracted to their own module so
-- per-axiom Parts/Ax*.agda files can import them without going through
-- this 16k-line file.  See BRA.Thm.EvalHelpers.

open import BRA.Thm.EvalHelpers public

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

  -- body_axI and body_axI_eval moved to BRA.Thm.Parts.AxI .
  -- body_axFst and body_axFst_eval moved to BRA.Thm.Parts.AxFst .
  -- body_axSnd and body_axSnd_eval moved to BRA.Thm.Parts.AxSnd .
  -- body_axConst and body_axConst_eval moved to BRA.Thm.Parts.AxConst .
  -- body_axComp and body_axComp_eval moved to BRA.Thm.Parts.AxComp .
  -- body_axComp2 and body_axComp2_eval moved to BRA.Thm.Parts.AxComp2 .

  -- axLift f a' b' : LHS = ap2 (Lift f) a' b' , RHS = ap1 f a'.
  --   payT depth 3: Pair cf (Pair payAT payBT).
  -- body_axLift and body_axLift_eval moved to BRA.Thm.Parts.AxLift .
  -- body_axPost and body_axPost_eval moved to BRA.Thm.Parts.AxPost .
  -- body_axFan and body_axFan_eval moved to BRA.Thm.Parts.AxFan .
  -- body_axZ and body_axZ_eval moved to BRA.Thm.Parts.AxKT .
  -- body_axRecLf and body_axRecLf_eval moved to BRA.Thm.Parts.AxRecLf .

  -- body_axRecNd and body_axRecNd_eval moved to BRA.Thm.Parts.AxRecNd .

  -- body_axIfLfL and body_axIfLfL_eval moved to BRA.Thm.Parts.AxIfLfL .
  -- body_axIfLfN and body_axIfLfN_eval moved to BRA.Thm.Parts.AxIfLfN .
  -- body_axTreeEqLL and body_axTreeEqLL_eval moved to BRA.Thm.Parts.AxTreeEqLL .
  -- body_axTreeEqLN and body_axTreeEqLN_eval moved to BRA.Thm.Parts.AxTreeEqLN .
  -- body_axTreeEqNL and body_axTreeEqNL_eval moved to BRA.Thm.Parts.AxTreeEqNL .
  -- body_axTreeEqNN and body_axTreeEqNN_eval moved to BRA.Thm.Parts.AxTreeEqNN .
  -- body_axGoodstein and body_axGoodstein_eval moved to BRA.Thm.Parts.AxGoodstein .
  -- body_axRefl and body_axRefl_eval moved to BRA.Thm.Parts.AxRefl .
  -- body_axEqTrans and body_axEqTrans_eval moved to BRA.Thm.Parts.AxEqTrans .
  -- body_axEqCong1 and body_axEqCong1_eval moved to BRA.Thm.Parts.AxEqCong1 .
  -- body_axEqCongL and body_axEqCongL_eval moved to BRA.Thm.Parts.AxEqCongL .
  -- body_axEqCongR and body_axEqCongR_eval moved to BRA.Thm.Parts.AxEqCongR .
  -- body_axK and body_axK_eval moved to BRA.Thm.Parts.AxK .
  -- body_axS and body_axS_eval moved to BRA.Thm.Parts.AxS .
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
  -- payTcoded).
  --
  -- Soundification swap (2026-05-03): body_ruleSym is the verifying
  -- body  body_ruleSym_v  from  BRA.SoundRuleSymProto :
  --   body_ruleSym_v = Post verifierRSF1 Pair
  -- where verifierRSF1 IfLf-gates on Pair-shape of Snd bb (the IH).
  -- Pass branch (Pair-shaped) does the swap; fail branch (leaf O)
  -- outputs codeTriv = falseT .  Consumers thread a Pair-shape
  -- witness on the IH through  body_ruleSym_v_eval_pass .
  body_ruleSym     : Fun2
  body_ruleSym     = body_ruleSym_v
  -- ruleTrans y1 y2: output is reify(codeFormula (atomic (eqn t v))) =
  -- Pair payT_r payV_r.  After distribution Snd b = Pair (thmT y1_r)
  -- (thmT y2_r) , the body extracts payT_r = Fst(thmT y1_r) and
  -- payV_r = Snd(thmT y2_r) and pairs them.  Body uses the
  -- postSndBody_eval (Comp Fst Fst / Comp Snd Snd) helpers internally.
  -- Soundification swap (2026-05-03): body_ruleTrans = body_ruleTrans_v.
  body_ruleTrans   : Fun2
  body_ruleTrans   = body_ruleTrans_v
  -- cong1 f y_h: output is reify(codeFormula(atomic (eqn (ap1 f t) (ap1 f u)))) =
  -- Pair (Pair K_a1 (Pair payF payT_r)) (Pair K_a1 (Pair payF payU_r)) where
  --   K_a1 = reify tagAp1, payF = reify(codeF1 f),
  --   payT_r = reify(code t), payU_r = reify(code u).
  -- After distribution Snd b = Pair (thmT payF) (thmT y_h_r) and IH on
  -- y_h_r = Pair payT_r payU_r:
  --   payF       = Fst(Snd a)               (from a directly; no distrib)
  --   payT_r     = Fst(Snd(Snd b))          (Fst of thmT y_h_r)
  --   payU_r     = Snd(Snd(Snd b))          (Snd of thmT y_h_r)
  -- Soundification swap (2026-05-03): body_cong1 = body_cong1_v from
  -- BRA.SoundCong1Proto, which IfLf-gates on the Pair-shape of
  -- Snd(Snd bb) (= thmT y_h_r , the IH).  Pass branch assembles the
  -- cong1 conclusion code; fail branch (leaf O) outputs codeTriv =
  -- falseT.  body_cong1_eval threads the IH Pair-shape witness via
  -- body_cong1_v_eval_pass.
  body_cong1       : Fun2
  body_cong1       = body_cong1_v
  -- congL g x y_h: output is reify(codeFormula(atomic(eqn (ap2 g t x) (ap2 g u x)))).
  -- New payload (Finding 1):  payT = Pair (Pair payG payX) y_h_r .  After
  -- two-level distribution
  --   Snd b = Pair (thmT (Pair payG payX)) (thmT y_h_r)
  -- and IH on  y_h_r = Pair payT_r payU_r , the body extracts:
  --   K_a2   = constant
  --   payG   = Fst(Fst(Snd a))                             [Comp Fst (Comp Fst Snd)]
  --   payX   = Snd(Fst(Snd a))                             [Comp Snd (Comp Fst Snd)]
  --   payT_r = Fst(Snd(Snd b))                             [post-Snd: Comp Fst Snd]
  --   payU_r = Snd(Snd(Snd b))                             [post-Snd: Comp Snd Snd]
  --
  -- Output: Pair (Pair K_a2 (Pair payG (Pair payT_r payX)))
  --              (Pair K_a2 (Pair payG (Pair payU_r payX))) .
  -- Soundification swap (2026-05-03): body_congL = body_congL_v from
  -- BRA.SoundCongLProto.  IfLf-gates on Pair-shape of  Snd(Snd bb)
  -- (= thmT y_h_r , the IH).  Pass branch assembles the congL conclusion
  -- code; fail branch outputs codeTriv.  body_congL_eval (closed/param/
  -- lifted/doublelifted) routes through body_congL_v_eval_pass*.
  body_congL       : Fun2
  body_congL       = body_congL_v
  -- congR g x y_h: similar to congL but the output's inner Pair has
  -- payX BEFORE payT_r/payU_r:
  --   reify(outCongR g x t u) =
  --     Pair (Pair K_a2 (Pair payG (Pair payX payT_r)))
  --          (Pair K_a2 (Pair payG (Pair payX payU_r)))
  -- Body has the same structure as body_congL with the inner-pair
  -- arguments swapped.
  -- Soundification swap (2026-05-03): body_congR = body_congR_v.
  body_congR       : Fun2
  body_congR       = body_congR_v
  -- mp y1 y2: output is reify(codeFormula Q).  After distribution
  -- Snd b = Pair (thmT y1_r) (thmT y2_r) , and IH1 says
  -- thmT y1_r = reify(codeFormula (P imp Q)) = Pair K_imp (Pair pT qT).
  -- Soundification swap (2026-05-03): body_mp is the verifying body
  --   body_mp_v = Post verifierF1 Pair
  -- from BRA.SoundMpProto.  verifierF1 checks
  --     Fst (thmT y1T) = tagImp     (outer head check)
  --   and
  --     thmT y2T = Fst (Snd (thmT y1T))   (inner check, the antecedent)
  -- and reduces to  Snd (Snd (thmT y1T)) = qT  on pass, codeTriv on fail.
  -- The eval lemmas below take an extra  dh : thmT y2T = pT  hypothesis
  -- and discharge the inner reflexivity  TreeEq pT pT = O  internally
  -- via  treeEqReflParam pT  (BRA.TreeEqReflParam).
  body_mp          : Fun2
  body_mp          = body_mp_v
  -- ruleInst x t y_h: output is reify(codeFormula(substF x t P)).
  -- The body computes  subT(<payVarX, payT_t>, codeFormulaP)  via the
  -- subT combinator from BRA.SubT (which lifts codedSubst to terms).
  --
  -- NEW PAYLOAD LAYOUT (refactor 2026-05-02): proof-index  y_h  sits at
  -- OUTER Snd of payT, the closed (varCode, tCode) pair sits at inner Fst.
  --   payT = Pair (Pair payVarX payT_t) y_h_r .
  --
  -- Extractors over  a = Pair tagCode_ruleInst payT :
  --   ARGS_extractor : Pair payVarX payT_t
  --     = Fst(Snd a)                                            -- closed.
  --   CODEP_extractor : thmT y_h_r
  --     = Snd(Snd b)  with  Snd b = thmT payT distrib'd to
  --       Pair (thmT (Pair payVarX payT_t)) (thmT y_h_r)
  --       via thmTDistrib_param at (Pair payVarX payT_t, y_h_r)
  --       (Fst-shape on Pair payVarX payT_t is CLOSED via axFst —
  --        no shape on y_h_r needed!).
  --
  -- body = Fan ARGS_extractor CODEP_extractor subT  so that
  --   ap2 body a b = ap2 subT (ARGS_extractor a b) (CODEP_extractor a b) .
  --
  -- Soundification swap (2026-05-03): body_ruleInst is now the verifying
  -- body  body_ruleInst_v  from  BRA.SoundRuleInstProto :
  --   body_ruleInst_v = Fan (Lift (Comp Fst Snd))
  --                          (Post (Comp Snd (Comp Snd Snd)) Pair)
  --                          verifyAndRun
  -- where  verifyAndRun = Post verifierRIF1 Pair  IfLf-gates the subT
  -- pipeline on the second extractor (thmT y_h).  Pass branch (thmT y_h
  -- is Pair-shaped) runs the original  subT(args, thmT_y_h) ; fail
  -- branch (thmT y_h = O leaf) outputs  codeTriv = falseT .  All
  -- existing  body_ruleInst_eval / _param / thmTDispRuleInst / _param
  -- consumers thread a new dh : codeP = Pair fst snd inner-check
  -- hypothesis through  body_ruleInst_v_eval_pass .
  body_ruleInst    : Fun2
  body_ruleInst    = body_ruleInst_v
  -- ruleIndBT: output is reify (codeFormula P), and codeFormula P sits
  -- at Fst(Snd a) since the encoding is
  --   nd tagRuleIndBT (nd (codeFormula P) (...)) .
  -- Body extracts Fst(Snd a) directly; no IH application needed.
  -- Soundification swap (2026-05-03): body_ruleIndBT = body_ruleIndBT_v.
  -- Original body  Lift (Comp Fst Snd)  is just a constant extractor of
  -- codeFP from the encoding (no IH consumption).  Verifying body
  -- IfLf-gates on  Snd a  being Pair-shaped.  Pass: codeFP.  Fail: codeTriv.
  body_ruleIndBT   : Fun2
  body_ruleIndBT   = body_ruleIndBT_v

  -- 4 safe-default-axiom bodies.  axFstLf, axSndLf, axIfLfLL have closed
  -- output (no parameters in the conclusion); body returns the closed
  -- encoded out via Lift (KT _).  axIfLfNL takes (x, y) parameters; its
  -- body extracts payX/payY from payload and builds the encoded LHS.

  -- body_axFstLf and body_axFstLf_eval moved to BRA.Thm.Parts.AxFstLf .
  -- body_axSndLf and body_axSndLf_eval moved to BRA.Thm.Parts.AxSndLf .

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
  -- Soundification swap (2026-05-03): body_ruleInst2 = body_ruleInst2_v.
  -- IfLf-gates on the IH (codeP) Pair-shape; pass branch runs subT2.
  -- body_ruleInst2_eval_param + thmTDispRuleInst2_param now require an
  -- explicit Pair-shape witness for codeP (supplied by the 3 Th12*
  -- callers from the concrete codeFormula(...) shape).
  body_ruleInst2   : Fun2
  body_ruleInst2   = body_ruleInst2_v

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
  -- checkTag_axRecLf / checkTag_axRecNd removed (axRecLf / axRecNd
  -- demoted to derived lemmas).
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
  checkTag_axTreeRecLf : Fun2
  checkTag_axTreeRecLf = Fan (Lift (KT tagCode_axTreeRecLf)) (Lift Fst) TreeEq
  checkTag_axTreeRecNd : Fun2
  checkTag_axTreeRecNd = Fan (Lift (KT tagCode_axTreeRecNd)) (Lift Fst) TreeEq

  ------------------------------------------------------------------
  -- branch + next combinators (build cascade bottom-up).
  --
  -- Cascade EXTENDED by the 4 safe-default axioms after ruleIndBT,
  -- the simultaneous double-substitution tag (tagRuleInst2) after axIfLfNL,
  -- and the unified tree-recursor tags (tagAxTreeRecLf, tagAxTreeRecNd)
  -- after tagRuleInst2:
  --   branch_ruleIndBT chains to next_ruleIndBT (-> checkTag_axFstLf).
  --   branch_axIfLfNL chains to next_axIfLfNL (-> checkTag_ruleInst2).
  --   branch_ruleInst2 chains to next_ruleInst2 (-> checkTag_axTreeRecLf).
  --   The chain ends at branch_axTreeRecNd = Fan body_axTreeRecNd fbBody Pair.

  branch_axTreeRecNd : Fun2
  branch_axTreeRecNd = Fan body_axTreeRecNd fbBody             Pair
  next_axTreeRecLf   : Fun2
  next_axTreeRecLf   = Fan checkTag_axTreeRecNd branch_axTreeRecNd IfLf
  branch_axTreeRecLf : Fun2
  branch_axTreeRecLf = Fan body_axTreeRecLf next_axTreeRecLf   Pair
  next_ruleInst2     : Fun2
  next_ruleInst2     = Fan checkTag_axTreeRecLf branch_axTreeRecLf IfLf
  branch_ruleInst2   : Fun2
  branch_ruleInst2   = Fan body_ruleInst2   next_ruleInst2     Pair
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
  -- next_axRecLf / branch_axRecLf / next_axRecNd / branch_axRecNd
  -- removed (axRecLf / axRecNd demoted).  next_axKT chains directly
  -- to checkTag_axIfLfL .
  next_axKT          : Fun2
  next_axKT          = Fan checkTag_axIfLfL     branch_axIfLfL     IfLf
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

  -- stepProtoWrapped: absorbs the  Pair O ...  wrapper introduced by
  --   Rec  (now defined as  Comp2 (treeRec Z s) Z I , so  axRecNd
  -- delivers RHS first arg = ap2 Pair O orig ).  Equationally
  --
  --   ap2 stepProtoWrapped (ap2 Pair O orig) recs
  --     = ap2 stepProto (Snd (ap2 Pair O orig)) recs
  --     = ap2 stepProto orig recs
  --
  -- so the dispatch logic is unchanged.
  stepProtoWrapped : Fun2
  stepProtoWrapped = Fan (Lift Snd) (Post Snd Pair) stepProto

  thmT : Fun1
  thmT = Rec stepProtoWrapped

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

  -- Term-level analog: codedSubstT preserves (codeF1 thmT) for any
  -- substituent Term (codeF1 thmT has no varCode_n substructure).
  -- Provable inside the abstract block where thmT unfolds; refl works
  -- because codedSubstT distributes through closed concrete codeF1 thmT
  -- with all-false treeEq comparisons.

  codedSubstT_codeF1Th_eq_reify :
    (x : Nat) (repl : Term) ->
    Eq (codedSubstT repl (code (var x)) (codeF1 thmT))
       (reify (codeF1 thmT))
  codedSubstT_codeF1Th_eq_reify x repl = refl

  -- Head-mismatch witnesses: tagVar mismatches codeF1 thmT (which starts
  -- with a different tag).  Used in subT_node_no_match witnesses when
  -- distributing through code (ap1 thmT _).

  treeEq_tagVar_codeF1Th_false :
    Eq (treeEq tagVar (codeF1 thmT)) false
  treeEq_tagVar_codeF1Th_false = refl

  -- The encoded "thmT(t)" Term-level lemma at SPECIFIC n = 1 (var 1).
  -- Specialised so that natCode (suc zero) = nd lf lf reduces and
  -- treeEq fires.  Used in K_part_l (step 4) for distributing subT
  -- through (code (ap1 thmT (var 1))).

  codedSubstT_code_thmT_var1 :
    (repl : Term) ->
    Eq (codedSubstT repl (code (var (suc zero)))
                    (code (ap1 thmT (var (suc zero)))))
       (ap2 Pair (reify tagAp1) (ap2 Pair (reify (codeF1 thmT)) repl))
  codedSubstT_code_thmT_var1 repl = refl

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
        -- New axRecNd shape: thmT(a) = stepProtoWrapped (Pair O a) recs.
        aW : Term
        aW = ap2 Pair O a
        e1a : Deriv (atomic (eqn (ap1 thmT a) (ap2 stepProtoWrapped aW b)))
        e1a = axRecNd stepProtoWrapped tag payT
        -- stepProtoWrapped (Pair O a) b
        --   = ap2 stepProto (Snd (Pair O a)) (Snd (Pair (Pair O a) b))
        --   = ap2 stepProto a b
        -- by axFan + axLift Snd + axPost Snd Pair + axSnd O a + axSnd (Pair O a) b.
        unfoldFan : Deriv (atomic (eqn (ap2 stepProtoWrapped aW b)
                                       (ap2 stepProto (ap2 (Lift Snd) aW b)
                                                       (ap2 (Post Snd Pair) aW b))))
        unfoldFan = axFan (Lift Snd) (Post Snd Pair) stepProto aW b
        -- ap2 (Lift Snd) aW b = Snd aW = a
        leftRed : Deriv (atomic (eqn (ap2 (Lift Snd) aW b) a))
        leftRed = ruleTrans (axLift Snd aW b) (axSnd O a)
        -- ap2 (Post Snd Pair) aW b = Snd (Pair aW b) = b
        rightRed : Deriv (atomic (eqn (ap2 (Post Snd Pair) aW b) b))
        rightRed = ruleTrans (axPost Snd Pair aW b) (axSnd aW b)
        congLft : Deriv (atomic (eqn (ap2 stepProto (ap2 (Lift Snd) aW b)
                                                     (ap2 (Post Snd Pair) aW b))
                                     (ap2 stepProto a (ap2 (Post Snd Pair) aW b))))
        congLft = congL stepProto (ap2 (Post Snd Pair) aW b) leftRed
        congRgt : Deriv (atomic (eqn (ap2 stepProto a (ap2 (Post Snd Pair) aW b))
                                     (ap2 stepProto a b)))
        congRgt = congR stepProto a rightRed
        e1 : Deriv (atomic (eqn (ap1 thmT a) (ap2 stepProto a b)))
        e1 = ruleTrans e1a (ruleTrans unfoldFan (ruleTrans congLft congRgt))
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

  -- body_axI_eval moved to BRA.Thm.Parts.AxI .

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
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axTreeEqLL payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxTreeEqLL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)   tagCode_axTreeEqLL payT b body_axIfLfN   next_axIfLfN
                  (teqDiff tagAxIfLfN   tagAxTreeEqLL refl)
        hh   = hitAtTag  (natCode tagAxTreeEqLL) tagCode_axTreeEqLL payT b body_axTreeEqLL next_axTreeEqLL
                  (teqEq tagAxTreeEqLL)
        be   = body_axTreeEqLL_eval b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans hh be)))))))))))))

  -- thmTDispAxRecLf removed: axRecLf demoted to a derived lemma
  -- (see BRA/Deriv.agda).

  thmTDispAxIfLfL : (a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxIfLfL a' b')))
                       (reify (outAxIfLfL a' b'))))
  thmTDispAxIfLfL a' b' =
    let payT = reify (nd (code a') (code b'))
        a    = ap2 Pair tagCode_axIfLfL payT
        b    = ap2 Pair (ap1 thmT tagCode_axIfLfL) (ap1 thmT payT)
        e1   = dispatchOpens tagAxKT payT
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
        hh   = hitAtTag  (natCode tagAxIfLfL)   tagCode_axIfLfL payT b body_axIfLfL   next_axIfLfL
                  (teqEq tagAxIfLfL)
        be   = body_axIfLfL_eval a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10
       (ruleTrans hh be)))))))))))

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
        e1   = dispatchOpens tagAxKT payT
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
        hh   = hitAtTag  (natCode tagAxIfLfL)   tagCode_axIfLfL payT b body_axIfLfL   next_axIfLfL
                  (teqEq tagAxIfLfL)
        be   = body_axIfLfL_eval_param aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10
       (ruleTrans hh be)))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans hh be))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans hh be)))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans hh be)))))))))))))))))

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
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axIfLfN payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxIfLfN refl)
        hh   = hitAtTag  (natCode tagAxIfLfN)   tagCode_axIfLfN payT b body_axIfLfN   next_axIfLfN
                  (teqEq tagAxIfLfN)
        be   = body_axIfLfN_eval x y a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans hh be))))))))))))

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
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axIfLfN payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxIfLfN refl)
        hh   = hitAtTag  (natCode tagAxIfLfN)   tagCode_axIfLfN payT b body_axIfLfN   next_axIfLfN
                  (teqEq tagAxIfLfN)
        be   = body_axIfLfN_eval_param xT yT aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans hh be))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans hh be))))))))))))))))

  -- thmTDispAxRecNd removed: axRecNd demoted to a derived lemma
  -- (see BRA/Deriv.agda).

  ------------------------------------------------------------------
  -- Group III non-recursive dispatch lemmas (axRefl, axEqTrans,
  -- axEqCong1, axEqCongL, axEqCongR).  The 5 recursive primitives
  -- (ruleSym, ruleTrans, cong1, congL, congR) are deferred.

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans hh be))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans hh be))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans hh be))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans hh be)))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans hh be))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans hh be)))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Group IV non-recursive dispatch lemmas (axK, axS, axNeg,
  -- axExFalso, axContrapos).  The 4 recursive primitives
  -- (mp, ruleInst, ruleIndBT) are deferred.

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans hh be))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans hh be)))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans hh be))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans hh be)))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35 (ruleTrans hh be))))))))))))))))))))))))))))))))

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
        -- reify(codeFormula(atomic(eqn t u))) reduces definitionally to
        -- ap2 Pair payTcoded payUcoded, so sndB_eq IS the Pair-shape
        -- witness the verifying body needs.
    in body_ruleSym_v_eval_pass a bb payTcoded payUcoded sndB_eq

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22
       (ruleTrans hh be)))))))))))))))))))

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
    let codeFP : Term
        codeFP = reify (codeFormula P)
        restT : Term
        restT = reify (nd (code (var v1))
                          (nd (code (var v2))
                              (nd y_base y_step)))
        a : Term
        a = ap2 Pair tagCode_ruleIndBT (ap2 Pair codeFP restT)
        encShape : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair codeFP restT)))
        encShape = axSnd tagCode_ruleIndBT (ap2 Pair codeFP restT)
    in body_ruleIndBT_v_eval_pass a bb codeFP restT encShape

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38
       (ruleTrans hh be)))))))))))))))))))))))))))))))))))

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
    let codeFP : Term
        codeFP = reify (codeFormula P)
        restT : Term
        restT = ap2 Pair (reify (code (var v1)))
                   (ap2 Pair (reify (code (var v2)))
                     (ap2 Pair y_base_T y_step_T))
        a : Term
        a = ap2 Pair tagCode_ruleIndBT (ap2 Pair codeFP restT)
        encShape : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair codeFP restT)))
        encShape = axSnd tagCode_ruleIndBT (ap2 Pair codeFP restT)
    in body_ruleIndBT_v_eval_pass a bb codeFP restT encShape

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38
       (ruleTrans hh be)))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- 4 safe-default-axiom dispatches (axFstLf, axSndLf, axIfLfLL,
  -- axIfLfNL).  Each cascade skips ALL 39 existing tags (axI..ruleIndBT)
  -- plus any earlier safe-default tags, then hits at its own tag.

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))

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
  -- Helper: unfold thmT (Pair u v) into stepProto (Pair u v) (recs)
  -- via axRecNd at stepProtoWrapped + Fan reductions (mirrors the body
  -- of dispatchOpens; factored out for thmTDistrib reuse).
  thmTUnfoldStep : (u v : Term) ->
    Deriv (atomic (eqn (ap1 thmT (ap2 Pair u v))
                       (ap2 stepProto (ap2 Pair u v)
                                       (ap2 Pair (ap1 thmT u) (ap1 thmT v)))))
  thmTUnfoldStep u v =
    let a : Term
        a = ap2 Pair u v
        b : Term
        b = ap2 Pair (ap1 thmT u) (ap1 thmT v)
        aW : Term
        aW = ap2 Pair O a
        e1a : Deriv (atomic (eqn (ap1 thmT a) (ap2 stepProtoWrapped aW b)))
        e1a = axRecNd stepProtoWrapped u v
        unfoldFan : Deriv (atomic (eqn (ap2 stepProtoWrapped aW b)
                                       (ap2 stepProto (ap2 (Lift Snd) aW b)
                                                       (ap2 (Post Snd Pair) aW b))))
        unfoldFan = axFan (Lift Snd) (Post Snd Pair) stepProto aW b
        leftRed : Deriv (atomic (eqn (ap2 (Lift Snd) aW b) a))
        leftRed = ruleTrans (axLift Snd aW b) (axSnd O a)
        rightRed : Deriv (atomic (eqn (ap2 (Post Snd Pair) aW b) b))
        rightRed = ruleTrans (axPost Snd Pair aW b) (axSnd aW b)
        congLft : Deriv (atomic (eqn (ap2 stepProto (ap2 (Lift Snd) aW b)
                                                     (ap2 (Post Snd Pair) aW b))
                                     (ap2 stepProto a (ap2 (Post Snd Pair) aW b))))
        congLft = congL stepProto (ap2 (Post Snd Pair) aW b) leftRed
        congRgt : Deriv (atomic (eqn (ap2 stepProto a (ap2 (Post Snd Pair) aW b))
                                     (ap2 stepProto a b)))
        congRgt = congR stepProto a rightRed
    in ruleTrans e1a (ruleTrans unfoldFan (ruleTrans congLft congRgt))

  thmTDistrib y1 y2 {x'} y1' shape =
    let a : Term
        a = ap2 Pair (reify y1) (reify y2)
        b' : Term
        b' = ap2 Pair (ap1 thmT (reify y1)) (ap1 thmT (reify y2))
        e1 : Deriv (atomic (eqn (ap1 thmT a) (ap2 stepProto a b')))
        e1 = thmTUnfoldStep (reify y1) (reify y2)
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
        e1 = thmTUnfoldStep y1T y2T
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
    -- IH dh (NEW for verifying body_mp_v): thmT (reify y2) = reify (codeFormula P) .
    Deriv (atomic (eqn (ap1 thmT (reify y2)) (reify (codeFormula P)))) ->
    Deriv (atomic (eqn
      (ap2 body_mp (ap2 Pair tagCode_mp (reify (nd y1 y2))) bb)
      (reify (outMp Q))))
  body_mp_eval P Q y1 y2 bb distH d1 dh =
    let a : Term
        a = ap2 Pair tagCode_mp (reify (nd y1 y2))
        pT : Term
        pT = reify (codeFormula P)
        qT : Term
        qT = reify (codeFormula Q)
        innerRefl : Deriv (atomic (eqn (ap2 TreeEq pT pT) O))
        innerRefl = treeEqReflParam pT
    in body_mp_v_eval_pass a bb
         (ap1 thmT (reify y1)) (ap1 thmT (reify y2)) pT qT
         distH d1 dh innerRefl

  thmTDispMp : (P Q : Formula) (y1 y2 : Tree) (y1' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y1)) (ap2 Pair O y1'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y1))
                       (reify (codeFormula (P imp Q))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y2))
                       (reify (codeFormula P)))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encMp y1 y2)))
                       (reify (outMp Q))))
  thmTDispMp P Q y1 y2 y1' shape d1 dh =
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
        be = body_mp_eval P Q y1 y2 b distH d1 dh
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans hh be)))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Parametric variant of body_mp_eval / thmTDispMp.
  --
  -- Takes y1T, y2T : Term (open proof-index Terms) and pT, qT : Term
  -- (the codes of P and Q expressed at Term level).  d1's RHS uses
  -- (Pair (reify tagImp) (Pair pT qT)) instead of (reify (codeFormula
  -- (P imp Q))) — equivalent under codeFormula (P imp Q) =
  -- nd tagImp (nd (codeFormula P) (codeFormula Q)).
  --
  -- Used by Theorem 14 Phase C (BRA/Th14Step3.agda etc.) where the
  -- mp-step's first argument is a runtime-built Term (e.g. f_part(x))
  -- rather than a closed reified Tree.

  body_mp_eval_param : (y1T y2T : Term) (bb : Term) (pT qT : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
    Deriv (atomic (eqn (ap1 thmT y1T)
                       (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    -- NEW dh: thmT y2T = pT (inner check the verifying body_mp_v consumes).
    Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->
    Deriv (atomic (eqn
      (ap2 body_mp (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) bb)
      qT))
  body_mp_eval_param y1T y2T bb pT qT distH d1 dh =
    let a : Term
        a = ap2 Pair tagCode_mp (ap2 Pair y1T y2T)
        innerRefl : Deriv (atomic (eqn (ap2 TreeEq pT pT) O))
        innerRefl = treeEqReflParam pT
    in body_mp_v_eval_pass a bb (ap1 thmT y1T) (ap1 thmT y2T) pT qT
         distH d1 dh innerRefl

  ------------------------------------------------------------------
  -- body_mp_eval_proj : projection-form variant of body_mp_eval_param.
  --
  -- Returns  Snd(Snd(thmT y1T))  -- the syntactic projection of the
  -- consequent out of the encoded implication.  With the verifying
  -- body_mp_v this requires the same hypotheses as body_mp_eval_param
  -- (verification must succeed for the projection to equal qT, which
  -- in turn equals Snd(Snd(thmT y1T)) via d1).

  body_mp_eval_proj : (y1T y2T : Term) (bb : Term) (pT qT : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
    Deriv (atomic (eqn (ap1 thmT y1T)
                       (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->
    Deriv (atomic (eqn
      (ap2 body_mp (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) bb)
      (ap1 Snd (ap1 Snd (ap1 thmT y1T)))))
  body_mp_eval_proj y1T y2T bb pT qT distH d1 dh =
    let tj1 : Term
        tj1 = ap1 thmT y1T
        K_imp : Term
        K_imp = reify tagImp
        -- be : ap2 body_mp ... = qT  (via verifying eval).
        be : Deriv (atomic (eqn
               (ap2 body_mp (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) bb) qT))
        be = body_mp_eval_param y1T y2T bb pT qT distH d1 dh
        -- bridge: qT = Snd (Snd tj1)  via  d1 .
        d1_snd : Deriv (atomic (eqn (ap1 Snd tj1)
                                     (ap1 Snd (ap2 Pair K_imp (ap2 Pair pT qT)))))
        d1_snd = cong1 Snd d1
        sx1 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair K_imp (ap2 Pair pT qT)))
                                  (ap2 Pair pT qT)))
        sx1 = axSnd K_imp (ap2 Pair pT qT)
        d1_snd_full : Deriv (atomic (eqn (ap1 Snd tj1) (ap2 Pair pT qT)))
        d1_snd_full = ruleTrans d1_snd sx1
        d1_sndsnd : Deriv (atomic (eqn (ap1 Snd (ap1 Snd tj1))
                                         (ap1 Snd (ap2 Pair pT qT))))
        d1_sndsnd = cong1 Snd d1_snd_full
        sx2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair pT qT)) qT))
        sx2 = axSnd pT qT
        sndSndTj1Eq : Deriv (atomic (eqn (ap1 Snd (ap1 Snd tj1)) qT))
        sndSndTj1Eq = ruleTrans d1_sndsnd sx2
        -- be : ... = qT ; ruleSym then trans: ... = Snd(Snd tj1).
    in ruleTrans be (ruleSym sndSndTj1Eq)

  thmTDispMp_param : (y1T y2T : Term) (y1' x' : Term) (pT qT : Term) ->
    Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (atomic (eqn (ap1 thmT y1T)
                       (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    -- NEW dh (load-bearing for body_mp_v): thmT y2T = pT .
    Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)))
      qT))
  thmTDispMp_param y1T y2T y1' x' pT qT shape d1 dh =
    let payT = ap2 Pair y1T y2T
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
                                      (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
        distrib = thmTDistrib_param y1T y2T {x' = x'} y1' shape
        distH : Deriv (atomic (eqn (ap1 Snd b)
                                    (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
        distH = ruleTrans sndB_unfold distrib
        be = body_mp_eval_param y1T y2T b pT qT distH d1 dh
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans hh be)))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- thmTDispMp_proj : projection-form variant of thmTDispMp_param.
  --
  -- Drops the d1 hypothesis (thmT y1T = Pair tagImp (Pair pT qT))
  -- and returns the Snd(Snd(thmT y1T)) projection directly.

  thmTDispMp_proj : (y1T y2T : Term) (y1' x' : Term) (pT qT : Term) ->
    Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (atomic (eqn (ap1 thmT y1T)
                       (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    Deriv (atomic (eqn (ap1 thmT y2T) pT)) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)))
      (ap1 Snd (ap1 Snd (ap1 thmT y1T)))))
  thmTDispMp_proj y1T y2T y1' x' pT qT shape d1 dh =
    let payT = ap2 Pair y1T y2T
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
                                      (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
        distrib = thmTDistrib_param y1T y2T {x' = x'} y1' shape
        distH : Deriv (atomic (eqn (ap1 Snd b)
                                    (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
        distH = ruleTrans sndB_unfold distrib
        be = body_mp_eval_proj y1T y2T b pT qT distH d1 dh
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans hh be)))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Lifted (under an arbitrary auxiliary formula P) variants of
  -- stepProto_else, thmTDistrib_param, body_mp_eval_param and
  -- thmTDispMp_param.
  --
  -- Theorem 14 Phase C consumers (Th14Step3.agda, Th14Step5.agda)
  -- carry their dispatcher hypotheses *under* the proof-recovery
  -- formula PrAtX x = atomic (eqn (thmT x) cG).  At those call sites
  -- the inner-check witnesses (step1_l, step2_l, step3_l, K_part_l)
  -- are themselves lifted and cannot be unwrapped without redoing the
  -- underlying  axImpRefl P  bridge.  The plain unlifted dispatcher
  -- thmTDispMp_param remains the ground truth for closed-Tree call
  -- sites; the lifted variant below is a thin wrapper that lifts each
  -- closed structural step via  liftAxiom P  and chains the
  -- non-closed steps via  liftedRuleTrans P / liftedCong1 P / liftedCongL P .
  --
  -- For Step 1B (this commit) the inner-check hypothesis is taken but
  -- *unused* because the underlying body_mp does not perform any
  -- check (still the V0 body_mp = Post (Comp (Comp Snd ...) ...) Pair).
  -- Step 1C will swap body_mp -> body_mp_v and make the inner-check
  -- load-bearing.

  stepProto_else_l : (P : Formula) (a b x y : Term) ->
    Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst a)) (ap2 Pair x y))) ->
    Deriv (P imp atomic (eqn (ap2 stepProto a b) b))
  stepProto_else_l P a b x y discPairL =
    let e1   = axFan discComb branchesTop IfLf a b
        e2a  = discComb_eval a b
        e2L  : Deriv (P imp atomic (eqn (ap2 discComb a b) (ap2 Pair x y)))
        e2L  = liftedRuleTrans P (ap2 discComb a b) (ap1 Fst (ap1 Fst a)) (ap2 Pair x y)
                 (liftAxiom P e2a) discPairL
        e3a  = axFan dispatch sndProj Pair a b
        e3b  = sndProj_eval a b
        e3   = ruleTrans e3a (congR Pair (ap2 dispatch a b) e3b)
        e4L  : Deriv (P imp atomic (eqn (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))
                                          (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))))
        e4L  = liftedCongL P IfLf (ap2 discComb a b) (ap2 Pair x y) (ap2 branchesTop a b) e2L
        e5   = congR IfLf (ap2 Pair x y) e3
        e6   = axIfLfN x y (ap2 dispatch a b) b
    in liftedRuleTrans P (ap2 stepProto a b)
         (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))
         b
         (liftAxiom P e1)
         (liftedRuleTrans P (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))
                            (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))
                            b
            e4L
            (liftedRuleTrans P (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))
                               (ap2 IfLf (ap2 Pair x y) (ap2 Pair (ap2 dispatch a b) b))
                               b
               (liftAxiom P e5) (liftAxiom P e6)))

  thmTDistrib_param_l : (P : Formula) (y1T y2T : Term) {x' : Term} (y1' : Term) ->
    Deriv (P imp atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (P imp atomic (eqn (ap1 thmT (ap2 Pair y1T y2T))
                              (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
  thmTDistrib_param_l P y1T y2T {x'} y1' shapeL =
    let a   = ap2 Pair y1T y2T
        b'  = ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)
        e1  = thmTUnfoldStep y1T y2T
        f1  = axFst y1T y2T
        f2  = cong1 Fst f1
        f3L : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst a)) (ap2 Pair x' y1')))
        f3L = liftedRuleTrans P (ap1 Fst (ap1 Fst a)) (ap1 Fst y1T) (ap2 Pair x' y1')
                 (liftAxiom P f2) shapeL
        e2L = stepProto_else_l P a b' x' y1' f3L
    in liftedRuleTrans P (ap1 thmT a) (ap2 stepProto a b') b'
         (liftAxiom P e1) e2L

  -- Lifted variant of body_mp_eval_param using body_mp_v_eval_pass_l.
  -- innerL is the lifted inner-check witness  P imp (thmT y2T = pT) .
  body_mp_eval_param_l : (P : Formula) (y1T y2T : Term) (bb : Term) (pT qT : Term) ->
    Deriv (P imp atomic (eqn (ap1 Snd bb)
                              (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y1T)
                              (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y2T) pT)) ->
    Deriv (P imp atomic (eqn
      (ap2 body_mp (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)) bb)
      qT))
  body_mp_eval_param_l P y1T y2T bb pT qT distHL d1L innerL =
    let a : Term
        a = ap2 Pair tagCode_mp (ap2 Pair y1T y2T)
        innerRefl : Deriv (atomic (eqn (ap2 TreeEq pT pT) O))
        innerRefl = treeEqReflParam pT
        innerReflL : Deriv (P imp atomic (eqn (ap2 TreeEq pT pT) O))
        innerReflL = liftAxiom P innerRefl
    in body_mp_v_eval_pass_l P a bb (ap1 thmT y1T) (ap1 thmT y2T) pT qT
         distHL d1L innerL innerReflL

  ------------------------------------------------------------------
  -- thmTDispMp_param_l : lifted variant of thmTDispMp_param.
  --
  -- The inner-check hypothesis  Deriv (P imp atomic (eqn (thmT y2T) pT))
  -- is taken but *currently unused* (Step 1B caveat); body_mp does not
  -- verify, so soundness rests on the caller passing a correct d1.
  -- Step 1C will swap body_mp -> body_mp_v and consume innerL.

  thmTDispMp_param_l : (P : Formula)
    (y1T y2T : Term) (y1' x' : Term) (pT qT : Term) ->
    Deriv (P imp atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y1T)
                              (ap2 Pair (reify tagImp) (ap2 Pair pT qT)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y2T) pT)) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_mp (ap2 Pair y1T y2T)))
      qT))
  thmTDispMp_param_l P y1T y2T y1' x' pT qT shapeL d1L innerL =
    let payT = ap2 Pair y1T y2T
        a    = ap2 Pair tagCode_mp payT
        b    = ap2 Pair (ap1 thmT tagCode_mp) (ap1 thmT payT)
        -- Closed prefix of the unlifted dispatcher.
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
        prefixClosed : Deriv (atomic (eqn (ap1 thmT a) (ap2 body_mp a b)))
        prefixClosed =
          ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
          (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
          (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
          (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
          (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
          (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
          (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
          (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
          (ruleTrans s36 hh))))))))))))))))))))))))))))))))
        prefixL : Deriv (P imp atomic (eqn (ap1 thmT a) (ap2 body_mp a b)))
        prefixL = liftAxiom P prefixClosed
        sndBunfoldL : Deriv (P imp atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndBunfoldL = liftAxiom P (axSnd (ap1 thmT tagCode_mp) (ap1 thmT payT))
        distribL : Deriv (P imp atomic (eqn (ap1 thmT payT)
                                              (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
        distribL = thmTDistrib_param_l P y1T y2T {x' = x'} y1' shapeL
        distHL : Deriv (P imp atomic (eqn (ap1 Snd b)
                                            (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))))
        distHL = liftedRuleTrans P (ap1 Snd b) (ap1 thmT payT)
                   (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T))
                   sndBunfoldL distribL
        beL : Deriv (P imp atomic (eqn (ap2 body_mp a b) qT))
        beL = body_mp_eval_param_l P y1T y2T b pT qT distHL d1L innerL
    in liftedRuleTrans P (ap1 thmT a) (ap2 body_mp a b) qT prefixL beL

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
    in body_ruleTrans_v_eval_pass a bb tj1 tj2 payT_r payU_r payU_r payV_r distH d1 d2

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans hh be))))))))))))))))))))

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
    in body_ruleTrans_v_eval_pass a bb tj1 tj2 u1 u2 u3 u4 distH d1 d2

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
        liftedDistH : Deriv (P imp atomic (eqn (ap1 Snd bb) (ap2 Pair tj1 tj2)))
        liftedDistH = liftAxiom P distH
    in body_ruleTrans_v_eval_pass_l P a bb tj1 tj2 u1 u2 u3 u4
         liftedDistH lifted_d1 lifted_d2

  -- Doubly-lifted body_ruleTrans_eval_param.
  body_ruleTrans_eval_param_doublelifted :
    (y1T y2T bb : Term) (u1 u2 u3 u4 : Term) ->
    (P1 P2 : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT y1T) (ap1 thmT y2T)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap2 body_ruleTrans (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)) bb)
      (ap2 Pair u1 u4))))
  body_ruleTrans_eval_param_doublelifted y1T y2T bb u1 u2 u3 u4 P1 P2 distH lifted_d1 lifted_d2 =
    let tj1 = ap1 thmT y1T
        tj2 = ap1 thmT y2T
        a   = ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)
        liftedDistH : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd bb) (ap2 Pair tj1 tj2))))
        liftedDistH = liftAxiomTwo P1 P2 distH
    in body_ruleTrans_v_eval_pass_dl P1 P2 a bb tj1 tj2 u1 u2 u3 u4
         liftedDistH lifted_d1 lifted_d2

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans hh be))))))))))))))))))))

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
                                              lifted_be))))))))))))))))))))
    in chain_lifted

  -- Doubly-lifted variant.
  thmTDispRuleTrans_param_doublelifted :
    (y1T y2T : Term) (u1 u2 u3 u4 : Term)
    (y1' : Term) (x' : Term)
    (P1 P2 : Formula) ->
    Deriv (atomic (eqn (ap1 Fst y1T) (ap2 Pair x' y1'))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y1T) (ap2 Pair u1 u2)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y2T) (ap2 Pair u3 u4)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleTrans (ap2 Pair y1T y2T)))
      (ap2 Pair u1 u4))))
  thmTDispRuleTrans_param_doublelifted y1T y2T u1 u2 u3 u4 y1' x' P1 P2
                                         shape lifted_d1 lifted_d2 =
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
        lifted_be = body_ruleTrans_eval_param_doublelifted y1T y2T b u1 u2 u3 u4 P1 P2 distH
                      lifted_d1 lifted_d2
        chain_lifted =
          liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 e1)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s1)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s2)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s3)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s4)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s5)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s6)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s7)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s8)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s9)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s10)
                    (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s15)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s16)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s17)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s18)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s19)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s20)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s21)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s22)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s23)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 hh)
                                              lifted_be))))))))))))))))))))
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
  fstReifyCodeF2 (treeRec f s) = mkSigma _ (axFst _ _)

  -- Head-shape lemma for  code (var x) : the variable encoding always
  -- starts with  nd tagVar (...)  where  tagVar = nd (nd (nd lf lf) lf) lf
  -- (a non-leaf), so reify of it is  Pair X O  with X non-trivial.
  -- Returns both  x' (the X)  and  y' (= O) , so ruleInst's dispatch
  -- can invoke the generalised  thmTDistrib .
  fstReifyCodeVar : (x : Nat) ->
    Sigma Term (\ x' -> Sigma Term (\ y' ->
      Deriv (atomic (eqn (ap1 Fst (reify (code (var x)))) (ap2 Pair x' y')))))
  fstReifyCodeVar x = mkSigma _ (mkSigma _ (axFst _ _))

  -- Pair-shape lemma for  Pair (reify (codeF2 g)) xT : the inner-Pair
  -- left position holds  reify (codeF2 g) , which itself is a  Pair X Y .
  -- Used by NEW-layout congL/congR dispatchers (Finding 1) where
  -- thmTDistrib_param's outer step needs a shape on  Fst (Pair payG xT) ,
  -- not on  y_h_T  (which now sits at the outer Snd).
  pairFstReifyCodeF2 : (g : Fun2) (xT : Term) ->
    Sigma Term (\ x' -> Sigma Term (\ y' ->
      Deriv (atomic (eqn (ap1 Fst (ap2 Pair (reify (codeF2 g)) xT)) (ap2 Pair x' y')))))
  pairFstReifyCodeF2 Pair          xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 Const         xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 (Lift f)      xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 (Post f h)    xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 (Fan h1 h2 h) xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 IfLf          xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 TreeEq        xT = mkSigma _ (mkSigma _ (axFst _ xT))
  pairFstReifyCodeF2 (treeRec f s) xT = mkSigma _ (mkSigma _ (axFst _ xT))

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

        ----------------------------------------------------------------
        -- Soundification path: route through body_cong1_v_eval_pass.
        --
        -- payFExt : Fst(Snd a) = payF.
        --   Snd a = ap2 Pair payF y_h_r ; Fst of that = payF.
        payFExt : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) payF))
        payFExt =
          ruleTrans (cong1 Fst (axSnd tagCode_cong1 (ap2 Pair payF y_h_r)))
                    (axFst payF y_h_r)

        -- ihShape : Snd(Snd bb) = Pair payT_r payU_r .
        --   Snd bb = Pair tjF tjH (via distH) ; Snd of that = tjH (= reify codeFormula(eqn t u)
        --     definitionally Pair payT_r payU_r via d_h).
        snd_distH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                        (ap1 Snd (ap2 Pair tjF tjH))))
        snd_distH = cong1 Snd distH
        snd_pair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair = axSnd tjF tjH
        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                      (ap2 Pair payT_r payU_r)))
        ihShape = ruleTrans snd_distH (ruleTrans snd_pair d_h)
    in body_cong1_v_eval_pass a bb payF payT_r payU_r payFExt ihShape

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans hh be)))))))))))))))))))))

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
    let payF : Term
        payF = reify (codeF1 f)
        tjF : Term
        tjF = ap1 thmT payF
        tjH : Term
        tjH = ap1 thmT y_h_T
        a : Term
        a = ap2 Pair tagCode_cong1 (ap2 Pair payF y_h_T)

        -- payFExt: Fst(Snd a) = payF.
        payFExt : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) payF))
        payFExt =
          ruleTrans (cong1 Fst (axSnd tagCode_cong1 (ap2 Pair payF y_h_T)))
                    (axFst payF y_h_T)

        -- ihShape: Snd(Snd bb) = Pair u1 u2 .
        snd_distH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                        (ap1 Snd (ap2 Pair tjF tjH))))
        snd_distH = cong1 Snd distH
        snd_pair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair = axSnd tjF tjH
        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                      (ap2 Pair u1 u2)))
        ihShape = ruleTrans snd_distH (ruleTrans snd_pair d_h)
    in body_cong1_v_eval_pass a bb payF u1 u2 payFExt ihShape

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans hh be)))))))))))))))))))))

  ------------------------------------------------------------------
  -- Helper: extract  ap1 X (Snd bb) -> ap1 X tjH  via cong1 X distH
  -- followed by a 4-step axComp chain unfolding Comp Z (Comp Fst Snd)
  -- on  Pair tjG (Pair tjH tjX) .  Takes a Term  tag  so it can be
  -- reused for congL and congR (only the outer tag differs).

  -- New layout (Finding 1):  a  has the IH-input  third  at its outer Snd
  -- (i.e.  a = Pair _ (Pair _ third) ), and  bb  is such that
  --  Snd bb = Pair _ (thmT third) .  The extractor uses
  --  Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair  to produce
  --  ap1 X (ap1 Snd (ap1 Snd bb))  =  ap1 X (thmT third) , then
  -- composes with the IH-derived  ap1 X (ap1 thmT third) = val .
  congLR_extractTj_new :
    (X : Fun1) (head : Term) (third : Term) (a bb : Term) (val : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT head)
                                 (ap1 thmT third)))) ->
    Deriv (atomic (eqn (ap1 X (ap1 thmT third)) val)) ->
    Deriv (atomic (eqn
      (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
      val))
  congLR_extractTj_new X head third a bb val distH X_tjH_eq =
    let tjH = ap1 thmT head
        tjT = ap1 thmT third
        outerP = ap2 Pair tjH tjT
        e_post : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
          (ap1 (Comp X Snd) (ap1 Snd bb))))
        e_post = postSndBody_eval (Comp X Snd) a bb
        e_dist : Deriv (atomic (eqn (ap1 (Comp X Snd) (ap1 Snd bb))
                                     (ap1 (Comp X Snd) outerP)))
        e_dist = cong1 (Comp X Snd) distH
        e_unfX : Deriv (atomic (eqn (ap1 (Comp X Snd) outerP)
                                     (ap1 X (ap1 Snd outerP))))
        e_unfX = axComp X Snd outerP
        e_snd : Deriv (atomic (eqn (ap1 Snd outerP) tjT))
        e_snd = axSnd tjH tjT
        e_X_snd : Deriv (atomic (eqn (ap1 X (ap1 Snd outerP)) (ap1 X tjT)))
        e_X_snd = cong1 X e_snd
        e_X_outer : Deriv (atomic (eqn (ap1 (Comp X Snd) outerP) (ap1 X tjT)))
        e_X_outer = ruleTrans e_unfX e_X_snd
        e_chain : Deriv (atomic (eqn
          (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
          (ap1 X tjT)))
        e_chain = ruleTrans e_post (ruleTrans e_dist e_X_outer)
    in ruleTrans e_chain X_tjH_eq

  -- Lifted version of  congLR_extractTj_new .
  congLR_extractTj_new_lifted :
    (P : Formula) (X : Fun1) (head third a bb val : Term) ->
    Deriv (P imp atomic (eqn (ap1 Snd bb)
                              (ap2 Pair (ap1 thmT head)
                                        (ap1 thmT third)))) ->
    Deriv (P imp atomic (eqn (ap1 X (ap1 thmT third)) val)) ->
    Deriv (P imp atomic (eqn
      (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
      val))
  congLR_extractTj_new_lifted P X head third a bb val lifted_distH lifted_X_tjH_eq =
    let tjH = ap1 thmT head
        tjT = ap1 thmT third
        outerP = ap2 Pair tjH tjT
        e_post = postSndBody_eval (Comp X Snd) a bb
        e_unfX = axComp X Snd outerP
        e_snd = axSnd tjH tjT
        e_X_snd = cong1 X e_snd
        e_X_outer = ruleTrans e_unfX e_X_snd
        lifted_e_post = liftAxiom P e_post
        lifted_e_dist : Deriv (P imp atomic (eqn (ap1 (Comp X Snd) (ap1 Snd bb))
                                                  (ap1 (Comp X Snd) outerP)))
        lifted_e_dist = liftedCong1 P (Comp X Snd) (ap1 Snd bb) outerP lifted_distH
        lifted_e_X_outer = liftAxiom P e_X_outer
        lifted_e_chain =
          liftedRuleTrans P
            (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
            (ap1 (Comp X Snd) (ap1 Snd bb))
            (ap1 X tjT)
            lifted_e_post
            (liftedRuleTrans P
              (ap1 (Comp X Snd) (ap1 Snd bb))
              (ap1 (Comp X Snd) outerP)
              (ap1 X tjT)
              lifted_e_dist
              lifted_e_X_outer)
    in liftedRuleTrans P
         (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
         (ap1 X tjT)
         val
         lifted_e_chain
         lifted_X_tjH_eq

  -- Doubly-lifted version of  congLR_extractTj_new .
  congLR_extractTj_new_doublelifted :
    (P1 P2 : Formula) (X : Fun1) (head third a bb val : Term) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd bb)
                              (ap2 Pair (ap1 thmT head)
                                        (ap1 thmT third))))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 X (ap1 thmT third)) val))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
      val)))
  congLR_extractTj_new_doublelifted P1 P2 X head third a bb val
                                     lifted_distH lifted_X_tjH_eq =
    let tjH = ap1 thmT head
        tjT = ap1 thmT third
        outerP = ap2 Pair tjH tjT
        e_post = postSndBody_eval (Comp X Snd) a bb
        e_unfX = axComp X Snd outerP
        e_snd = axSnd tjH tjT
        e_X_snd = cong1 X e_snd
        e_X_outer = ruleTrans e_unfX e_X_snd
        lifted_e_post = liftAxiomTwo P1 P2 e_post
        lifted_e_dist : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 (Comp X Snd) (ap1 Snd bb))
               (ap1 (Comp X Snd) outerP))))
        lifted_e_dist = liftedCong1Two P1 P2 (Comp X Snd)
                          (ap1 Snd bb) outerP lifted_distH
        lifted_e_X_outer = liftAxiomTwo P1 P2 e_X_outer
        lifted_e_chain =
          liftedRuleTransTwo P1 P2
            (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
            (ap1 (Comp X Snd) (ap1 Snd bb))
            (ap1 X tjT)
            lifted_e_post
            (liftedRuleTransTwo P1 P2
              (ap1 (Comp X Snd) (ap1 Snd bb))
              (ap1 (Comp X Snd) outerP)
              (ap1 X tjT)
              lifted_e_dist
              lifted_e_X_outer)
    in liftedRuleTransTwo P1 P2
         (ap2 (Post (Comp (Comp X Snd) (Comp Snd Snd)) Pair) a bb)
         (ap1 X tjT)
         val
         lifted_e_chain
         lifted_X_tjH_eq

  body_congL_eval : (g : Fun2) (x : Term) (t u : Term) (y_h : Tree)
                    (bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g))
                                                      (reify (code x))))
                                 (ap1 thmT (reify y_h))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (reify (nd (nd (codeF2 g) (code x)) y_h)))
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
        a = ap2 Pair tagCode_congL (ap2 Pair (ap2 Pair payG payX) y_h_r)
        payT_r : Term
        payT_r = reify (code t)
        payU_r : Term
        payU_r = reify (code u)
        tjF : Term
        tjF = ap1 thmT (ap2 Pair payG payX)
        tjH : Term
        tjH = ap1 thmT y_h_r

        -- Extract  ap1 Snd a = Pair (Pair payG payX) y_h_r .
        sndAEq : Deriv (atomic (eqn (ap1 Snd a)
                                     (ap2 Pair (ap2 Pair payG payX) y_h_r)))
        sndAEq = axSnd tagCode_congL (ap2 Pair (ap2 Pair payG payX) y_h_r)

        -- payGExt : ap1 Fst (ap1 Fst (ap1 Snd a)) = payG .
        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG payX)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq)
                              (axFst (ap2 Pair payG payX) y_h_r)
        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG payX)

        -- payXExt : ap1 Snd (ap1 Fst (ap1 Snd a)) = payX .
        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG payX)

        -- ihShape : ap1 Snd (ap1 Snd bb) = ap2 Pair payT_r payU_r .
        snd_distH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                        (ap1 Snd (ap2 Pair tjF tjH))))
        snd_distH = cong1 Snd distH
        snd_pair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair = axSnd tjF tjH
        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                      (ap2 Pair payT_r payU_r)))
        ihShape = ruleTrans snd_distH (ruleTrans snd_pair d_h)
    in body_congL_v_eval_pass a bb payG payX payT_r payU_r payGExt payXExt ihShape

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
        -- New layout (Finding 1): outer pair = Pair (Pair payG payX) y_h_r
        innerLT : Term
        innerLT = ap2 Pair payG payX
        payT = ap2 Pair innerLT y_h_r
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
        -- distrib over the outer  Pair innerLT y_h_r ; shape on  Fst innerLT
        -- (innerLT = Pair payG payX is closed Pair-shaped via pairFstReifyCodeF2).
        shapeInner : Sigma Term (\ x' -> Sigma Term (\ y' ->
          Deriv (atomic (eqn (ap1 Fst innerLT) (ap2 Pair x' y')))))
        shapeInner = pairFstReifyCodeF2 g payX
        distrib : Deriv (atomic (eqn (ap1 thmT payT)
          (ap2 Pair (ap1 thmT innerLT) (ap1 thmT y_h_r))))
        distrib = thmTDistrib_param innerLT y_h_r {fst shapeInner}
                    (fst (snd shapeInner)) (snd (snd shapeInner))
        distH : Deriv (atomic (eqn (ap1 Snd b)
          (ap2 Pair (ap1 thmT innerLT) (ap1 thmT y_h_r))))
        distH = ruleTrans sndB_unfold distrib
        be = body_congL_eval g x t u y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans hh be))))))))))))))))))))))

  -- Parametric variant of body_congL_eval (Theorem 12 / Parts/Comp2.agda etc.).
  -- New payload (Finding 1):  Pair tag (Pair (Pair payG xT) y_h_T) .
  -- distH is now over  Snd bb = Pair (thmT (Pair payG xT)) (thmT y_h_T) ,
  -- supplied by the caller (or by  thmTDispCongL_param  via  thmTDistrib).
  body_congL_eval_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g)) xT))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  body_congL_eval_param g xT y_h_T u1 u2 bb distH d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congL (ap2 Pair (ap2 Pair payG xT) y_h_T)
        tjF  = ap1 thmT (ap2 Pair payG xT)
        tjH  = ap1 thmT y_h_T

        sndAEq : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair (ap2 Pair payG xT) y_h_T)))
        sndAEq = axSnd tagCode_congL (ap2 Pair (ap2 Pair payG xT) y_h_T)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG xT)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq) (axFst (ap2 Pair payG xT) y_h_T)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG xT)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG xT)

        snd_distH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                        (ap1 Snd (ap2 Pair tjF tjH))))
        snd_distH = cong1 Snd distH
        snd_pair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair = axSnd tjF tjH
        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair u1 u2)))
        ihShape = ruleTrans snd_distH (ruleTrans snd_pair d_h)
    in body_congL_v_eval_pass a bb payG xT u1 u2 payGExt payXExt ihShape

  -- Lifted version of body_congL_eval_param.  New layout (Finding 1).
  body_congL_eval_param_lifted : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g)) xT))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  body_congL_eval_param_lifted g xT y_h_T u1 u2 bb P distH lifted_d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congL (ap2 Pair (ap2 Pair payG xT) y_h_T)
        tjF  = ap1 thmT (ap2 Pair payG xT)
        tjH  = ap1 thmT y_h_T

        sndAEq : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair (ap2 Pair payG xT) y_h_T)))
        sndAEq = axSnd tagCode_congL (ap2 Pair (ap2 Pair payG xT) y_h_T)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG xT)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq) (axFst (ap2 Pair payG xT) y_h_T)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG xT)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG xT)

        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                      (ap1 Snd (ap2 Pair tjF tjH))))
        ihShape = cong1 Snd distH
        sndPair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        sndPair = axSnd tjF tjH
        sndSndBbEqTjH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH))
        sndSndBbEqTjH = ruleTrans ihShape sndPair

        liftedSndSndBb : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH))
        liftedSndSndBb = liftAxiom P sndSndBbEqTjH
        liftedIhShape : Deriv (P imp atomic
          (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair u1 u2)))
        liftedIhShape = liftedRuleTrans P (ap1 Snd (ap1 Snd bb)) tjH
                          (ap2 Pair u1 u2) liftedSndSndBb lifted_d_h

        payGExtL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExtL = liftAxiom P payGExt

        payXExtL : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExtL = liftAxiom P payXExt
    in body_congL_v_eval_pass_l P a bb payG xT u1 u2 payGExtL payXExtL liftedIhShape

  -- Doubly-lifted body_congL_eval_param.  New layout (Finding 1).
  body_congL_eval_param_doublelifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    (P1 P2 : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g)) xT))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap2 body_congL
            (ap2 Pair tagCode_congL
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT)))))))
  body_congL_eval_param_doublelifted g xT y_h_T u1 u2 bb P1 P2 distH lifted_d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congL (ap2 Pair (ap2 Pair payG xT) y_h_T)
        tjF  = ap1 thmT (ap2 Pair payG xT)
        tjH  = ap1 thmT y_h_T

        sndAEq : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair (ap2 Pair payG xT) y_h_T)))
        sndAEq = axSnd tagCode_congL (ap2 Pair (ap2 Pair payG xT) y_h_T)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG xT)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq) (axFst (ap2 Pair payG xT) y_h_T)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG xT)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG xT)

        ihStep : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                     (ap1 Snd (ap2 Pair tjF tjH))))
        ihStep = cong1 Snd distH
        sndPair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        sndPair = axSnd tjF tjH
        sndSndBbEqTjH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH))
        sndSndBbEqTjH = ruleTrans ihStep sndPair

        liftedSndSndBb : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH)))
        liftedSndSndBb = liftAxiomTwo P1 P2 sndSndBbEqTjH
        liftedIhShape : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair u1 u2))))
        liftedIhShape =
          liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 Snd bb)) tjH (ap2 Pair u1 u2)
            liftedSndSndBb lifted_d_h

        payGExtL : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG)))
        payGExtL = liftAxiomTwo P1 P2 payGExt

        payXExtL : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT)))
        payXExtL = liftAxiomTwo P1 P2 payXExt
    in body_congL_v_eval_pass_dl P1 P2 a bb payG xT u1 u2
         payGExtL payXExtL liftedIhShape

  -- Parametric variant of thmTDispCongL.
  -- New layout (Finding 1): payload =  Pair (Pair payG xT) y_h_T  with
  -- the open IH subterm  y_h_T  at the outer Snd, so the thmT-distribution
  -- Fst-walk only crosses the closed pair  (payG , xT)  (shape via
  -- pairFstReifyCodeF2).  No shape obligation on  y_h_T  is required.
  thmTDispCongL_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congL
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  thmTDispCongL_param g xT y_h_T u1 u2 d_h =
    let payG = reify (codeF2 g)
        innerLT : Term
        innerLT = ap2 Pair payG xT
        payT = ap2 Pair innerLT y_h_T
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
        shapeInner = pairFstReifyCodeF2 g xT
        distrib  = thmTDistrib_param innerLT y_h_T {fst shapeInner}
                     (fst (snd shapeInner)) (snd (snd shapeInner))
        distH    = ruleTrans sndB_unfold distrib
        be       = body_congL_eval_param g xT y_h_T u1 u2 b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans hh be))))))))))))))))))))))

  -- Lifted version of thmTDispCongL_param.  New layout (Finding 1).
  -- All closed sub-Derivs (e1, s1..s25, hh, distH) are liftAxiom'd;
  -- be uses body_congL_eval_param_lifted with the lifted d_h.
  thmTDispCongL_param_lifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
    (P : Formula) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congL
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT))))))
  thmTDispCongL_param_lifted g xT y_h_T u1 u2 P lifted_d_h =
    let payG = reify (codeF2 g)
        innerLT : Term
        innerLT = ap2 Pair payG xT
        payT = ap2 Pair innerLT y_h_T
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
        shapeInner = pairFstReifyCodeF2 g xT
        distrib  = thmTDistrib_param innerLT y_h_T {fst shapeInner}
                     (fst (snd shapeInner)) (snd (snd shapeInner))
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
                                              lifted_be))))))))))))))))))))))
    in chain_lifted

  -- Doubly-lifted thmTDispCongL_param.  New layout (Finding 1).
  thmTDispCongL_param_doublelifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
    (P1 P2 : Formula) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congL
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u1 xT)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair u2 xT)))))))
  thmTDispCongL_param_doublelifted g xT y_h_T u1 u2 P1 P2 lifted_d_h =
    let payG = reify (codeF2 g)
        innerLT : Term
        innerLT = ap2 Pair payG xT
        payT = ap2 Pair innerLT y_h_T
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
        shapeInner = pairFstReifyCodeF2 g xT
        distrib  = thmTDistrib_param innerLT y_h_T {fst shapeInner}
                     (fst (snd shapeInner)) (snd (snd shapeInner))
        distH    = ruleTrans sndB_unfold distrib
        lifted_be = body_congL_eval_param_doublelifted g xT y_h_T u1 u2 b P1 P2 distH lifted_d_h
        chain_lifted =
          liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 e1)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s1)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s2)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s3)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s4)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s5)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s6)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s7)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s8)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s9)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s10)
                    (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s15)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s16)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s17)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s18)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s19)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s20)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s21)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s22)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s23)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s24)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s25)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 hh)
                                              lifted_be))))))))))))))))))))))
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
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g))
                                                      (reify (code x))))
                                 (ap1 thmT (reify y_h))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (reify (nd (nd (codeF2 g) (code x)) y_h)))
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
        a = ap2 Pair tagCode_congR (ap2 Pair (ap2 Pair payG payX) y_h_r)
        payT_r : Term
        payT_r = reify (code t)
        payU_r : Term
        payU_r = reify (code u)
        tjF : Term
        tjF = ap1 thmT (ap2 Pair payG payX)
        tjH : Term
        tjH = ap1 thmT y_h_r

        sndAEq : Deriv (atomic (eqn (ap1 Snd a)
                                     (ap2 Pair (ap2 Pair payG payX) y_h_r)))
        sndAEq = axSnd tagCode_congR (ap2 Pair (ap2 Pair payG payX) y_h_r)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG payX)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq)
                              (axFst (ap2 Pair payG payX) y_h_r)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG payX)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) payX))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG payX)

        snd_distH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                        (ap1 Snd (ap2 Pair tjF tjH))))
        snd_distH = cong1 Snd distH
        snd_pair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair = axSnd tjF tjH
        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                      (ap2 Pair payT_r payU_r)))
        ihShape = ruleTrans snd_distH (ruleTrans snd_pair d_h)
    in body_congR_v_eval_pass a bb payG payX payT_r payU_r payGExt payXExt ihShape

  thmTDispCongR : (g : Fun2) (x : Term) (t u : Term) (y_h : Tree)
                  (y_h' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula (atomic (eqn t u)))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encCongR g x y_h)))
                       (reify (outCongR g x t u))))
  thmTDispCongR g x t u y_h y_h' shape_h d_h =
    let payG : Term
        payG = reify (codeF2 g)
        y_h_r : Term
        y_h_r = reify y_h
        payX : Term
        payX = reify (code x)
        -- New layout (Finding 1): outer pair = Pair (Pair payG payX) y_h_r
        innerLT : Term
        innerLT = ap2 Pair payG payX
        payT = ap2 Pair innerLT y_h_r
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
        shapeInner : Sigma Term (\ x' -> Sigma Term (\ y' ->
          Deriv (atomic (eqn (ap1 Fst innerLT) (ap2 Pair x' y')))))
        shapeInner = pairFstReifyCodeF2 g payX
        distrib : Deriv (atomic (eqn (ap1 thmT payT)
          (ap2 Pair (ap1 thmT innerLT) (ap1 thmT y_h_r))))
        distrib = thmTDistrib_param innerLT y_h_r {fst shapeInner}
                    (fst (snd shapeInner)) (snd (snd shapeInner))
        distH : Deriv (atomic (eqn (ap1 Snd b)
          (ap2 Pair (ap1 thmT innerLT) (ap1 thmT y_h_r))))
        distH = ruleTrans sndB_unfold distrib
        be = body_congR_eval g x t u y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans hh be)))))))))))))))))))))))

  -- Parametric variant of body_congR_eval (Theorem 12 / Comp2/Fan etc.).
  -- New payload (Finding 1):  Pair tag (Pair (Pair payG xT) y_h_T) .
  -- distH is now over  Snd bb = Pair (thmT (Pair payG xT)) (thmT y_h_T) ,
  -- supplied by the caller (or by  thmTDispCongR_param  via  thmTDistrib).
  body_congR_eval_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g)) xT))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  body_congR_eval_param g xT y_h_T u1 u2 bb distH d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congR (ap2 Pair (ap2 Pair payG xT) y_h_T)
        tjF  = ap1 thmT (ap2 Pair payG xT)
        tjH  = ap1 thmT y_h_T

        sndAEq : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair (ap2 Pair payG xT) y_h_T)))
        sndAEq = axSnd tagCode_congR (ap2 Pair (ap2 Pair payG xT) y_h_T)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG xT)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq) (axFst (ap2 Pair payG xT) y_h_T)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG xT)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG xT)

        snd_distH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                        (ap1 Snd (ap2 Pair tjF tjH))))
        snd_distH = cong1 Snd distH
        snd_pair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        snd_pair = axSnd tjF tjH
        ihShape : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair u1 u2)))
        ihShape = ruleTrans snd_distH (ruleTrans snd_pair d_h)
    in body_congR_v_eval_pass a bb payG xT u1 u2 payGExt payXExt ihShape

  -- Lifted version of body_congR_eval_param.  New layout (Finding 1).
  body_congR_eval_param_lifted : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    (P : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g)) xT))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  body_congR_eval_param_lifted g xT y_h_T u1 u2 bb P distH lifted_d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congR (ap2 Pair (ap2 Pair payG xT) y_h_T)
        tjF  = ap1 thmT (ap2 Pair payG xT)
        tjH  = ap1 thmT y_h_T

        sndAEq : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair (ap2 Pair payG xT) y_h_T)))
        sndAEq = axSnd tagCode_congR (ap2 Pair (ap2 Pair payG xT) y_h_T)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG xT)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq) (axFst (ap2 Pair payG xT) y_h_T)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG xT)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG xT)

        ihStep : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                     (ap1 Snd (ap2 Pair tjF tjH))))
        ihStep = cong1 Snd distH
        sndPair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        sndPair = axSnd tjF tjH
        sndSndBbEqTjH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH))
        sndSndBbEqTjH = ruleTrans ihStep sndPair

        liftedSndSndBb : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH))
        liftedSndSndBb = liftAxiom P sndSndBbEqTjH
        liftedIhShape : Deriv (P imp atomic
          (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair u1 u2)))
        liftedIhShape = liftedRuleTrans P (ap1 Snd (ap1 Snd bb)) tjH
                          (ap2 Pair u1 u2) liftedSndSndBb lifted_d_h

        payGExtL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExtL = liftAxiom P payGExt

        payXExtL : Deriv (P imp atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExtL = liftAxiom P payXExt
    in body_congR_v_eval_pass_l P a bb payG xT u1 u2 payGExtL payXExtL liftedIhShape

  -- Doubly-lifted body_congR_eval_param.  New layout (Finding 1).
  body_congR_eval_param_doublelifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 bb : Term) ->
    (P1 P2 : Formula) ->
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (codeF2 g)) xT))
                                 (ap1 thmT y_h_T)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap2 body_congR
            (ap2 Pair tagCode_congR
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T))
            bb)
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2)))))))
  body_congR_eval_param_doublelifted g xT y_h_T u1 u2 bb P1 P2 distH lifted_d_h =
    let payG = reify (codeF2 g)
        a    = ap2 Pair tagCode_congR (ap2 Pair (ap2 Pair payG xT) y_h_T)
        tjF  = ap1 thmT (ap2 Pair payG xT)
        tjH  = ap1 thmT y_h_T

        sndAEq : Deriv (atomic (eqn (ap1 Snd a) (ap2 Pair (ap2 Pair payG xT) y_h_T)))
        sndAEq = axSnd tagCode_congR (ap2 Pair (ap2 Pair payG xT) y_h_T)

        fstSndAEq : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) (ap2 Pair payG xT)))
        fstSndAEq = ruleTrans (cong1 Fst sndAEq) (axFst (ap2 Pair payG xT) y_h_T)

        payGExt : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG))
        payGExt = ruleTrans (cong1 Fst fstSndAEq) (axFst payG xT)

        payXExt : Deriv (atomic (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT))
        payXExt = ruleTrans (cong1 Snd fstSndAEq) (axSnd payG xT)

        ihStep : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb))
                                     (ap1 Snd (ap2 Pair tjF tjH))))
        ihStep = cong1 Snd distH
        sndPair : Deriv (atomic (eqn (ap1 Snd (ap2 Pair tjF tjH)) tjH))
        sndPair = axSnd tjF tjH
        sndSndBbEqTjH : Deriv (atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH))
        sndSndBbEqTjH = ruleTrans ihStep sndPair

        liftedSndSndBb : Deriv (P1 imp (P2 imp atomic (eqn (ap1 Snd (ap1 Snd bb)) tjH)))
        liftedSndSndBb = liftAxiomTwo P1 P2 sndSndBbEqTjH
        liftedIhShape : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 Snd (ap1 Snd bb)) (ap2 Pair u1 u2))))
        liftedIhShape =
          liftedRuleTransTwo P1 P2 (ap1 Snd (ap1 Snd bb)) tjH (ap2 Pair u1 u2)
            liftedSndSndBb lifted_d_h

        payGExtL : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 Fst (ap1 Fst (ap1 Snd a))) payG)))
        payGExtL = liftAxiomTwo P1 P2 payGExt

        payXExtL : Deriv (P1 imp (P2 imp atomic
          (eqn (ap1 Snd (ap1 Fst (ap1 Snd a))) xT)))
        payXExtL = liftAxiomTwo P1 P2 payXExt
    in body_congR_v_eval_pass_dl P1 P2 a bb payG xT u1 u2
         payGExtL payXExtL liftedIhShape

  -- Parametric variant of thmTDispCongR.
  -- New layout (Finding 1): payload =  Pair (Pair payG xT) y_h_T .
  thmTDispCongR_param : (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term) ->
    Deriv (atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congR
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  thmTDispCongR_param g xT y_h_T u1 u2 d_h =
    let payG = reify (codeF2 g)
        innerLT : Term
        innerLT = ap2 Pair payG xT
        payT = ap2 Pair innerLT y_h_T
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
        shapeInner = pairFstReifyCodeF2 g xT
        distrib  = thmTDistrib_param innerLT y_h_T {fst shapeInner}
                     (fst (snd shapeInner)) (snd (snd shapeInner))
        distH    = ruleTrans sndB_unfold distrib
        be       = body_congR_eval_param g xT y_h_T u1 u2 b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans hh be)))))))))))))))))))))))

  -- Lifted version of thmTDispCongR_param.  New layout (Finding 1).
  thmTDispCongR_param_lifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
    (P : Formula) ->
    Deriv (P imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2))) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congR
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2))))))
  thmTDispCongR_param_lifted g xT y_h_T u1 u2 P lifted_d_h =
    let payG = reify (codeF2 g)
        innerLT : Term
        innerLT = ap2 Pair payG xT
        payT = ap2 Pair innerLT y_h_T
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
        shapeInner = pairFstReifyCodeF2 g xT
        distrib  = thmTDistrib_param innerLT y_h_T {fst shapeInner}
                     (fst (snd shapeInner)) (snd (snd shapeInner))
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
                                              lifted_be)))))))))))))))))))))))
    in chain_lifted

  -- Doubly-lifted thmTDispCongR_param.  New layout (Finding 1).
  thmTDispCongR_param_doublelifted :
    (g : Fun2) (xT : Term) (y_h_T : Term) (u1 u2 : Term)
    (P1 P2 : Formula) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap1 thmT y_h_T) (ap2 Pair u1 u2)))) ->
    Deriv (P1 imp (P2 imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_congR
                  (ap2 Pair (ap2 Pair (reify (codeF2 g)) xT) y_h_T)))
      (ap2 Pair (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u1)))
                (ap2 Pair (reify tagAp2)
                          (ap2 Pair (reify (codeF2 g))
                                    (ap2 Pair xT u2)))))))
  thmTDispCongR_param_doublelifted g xT y_h_T u1 u2 P1 P2 lifted_d_h =
    let payG = reify (codeF2 g)
        innerLT : Term
        innerLT = ap2 Pair payG xT
        payT = ap2 Pair innerLT y_h_T
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
        shapeInner = pairFstReifyCodeF2 g xT
        distrib  = thmTDistrib_param innerLT y_h_T {fst shapeInner}
                     (fst (snd shapeInner)) (snd (snd shapeInner))
        distH    = ruleTrans sndB_unfold distrib
        lifted_be = body_congR_eval_param_doublelifted g xT y_h_T u1 u2 b P1 P2 distH lifted_d_h
        chain_lifted =
          liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 e1)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s1)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s2)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s3)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s4)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s5)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s6)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s7)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s8)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s9)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s10)
                    (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s15)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s16)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s17)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s18)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s19)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s20)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s21)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s22)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s23)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s24)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s25)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 s26)
          (liftedRuleTransTwo P1 P2 _ _ _ (liftAxiomTwo P1 P2 hh)
                                              lifted_be)))))))))))))))))))))))
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
    -- distH: Snd bb = Pair (thmT (Pair payVarX payT_t)) (thmT y_h_r) .
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (code (var x)))
                                                     (reify (code t))))
                                 (ap1 thmT (reify y_h))))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula P)))) ->
    Deriv (atomic (eqn
      (ap2 body_ruleInst
            (ap2 Pair tagCode_ruleInst
                  (reify (nd (nd (code (var x)) (code t)) y_h)))
            bb)
      (reify (outRuleInst x t P))))
  body_ruleInst_eval x t P y_h bb distH d_h =
    let payVarX : Term
        payVarX = reify (code (var x))
        payT_t : Term
        payT_t = reify (code t)
        y_h_r : Term
        y_h_r = reify y_h
        argsPair : Term
        argsPair = ap2 Pair payVarX payT_t
        a : Term
        a = ap2 Pair tagCode_ruleInst (ap2 Pair argsPair y_h_r)
        codeFP : Term
        codeFP = reify (codeFormula P)

        -- argsExt witness: Fst(Snd a) = argsPair via axSnd + axFst.
        argsExt : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) argsPair))
        argsExt = ruleTrans (cong1 Fst (axSnd tagCode_ruleInst (ap2 Pair argsPair y_h_r)))
                            (axFst argsPair y_h_r)

        -- Pair-shape of reify(codeFormula P) via codeFormulaPairShape.
        shapeP = codeFormulaPairShape P
        fp : Term
        fp = fst shapeP
        sp : Term
        sp = fst (snd shapeP)
        reifyPairEq : Deriv (atomic (eqn codeFP (ap2 Pair fp sp)))
        reifyPairEq = snd (snd shapeP)

        -- dh: ap1 thmT y_h_r = Pair fp sp (combine d_h with reifyPairEq).
        dh : Deriv (atomic (eqn (ap1 thmT y_h_r) (ap2 Pair fp sp)))
        dh = ruleTrans d_h reifyPairEq

        -- Apply the verifying body's eval pass.
        bodyEval : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
                                       (ap2 subT argsPair (ap1 thmT y_h_r))))
        bodyEval = body_ruleInst_v_eval_pass a bb argsPair
                     (ap1 thmT argsPair) (ap1 thmT y_h_r) fp sp
                     argsExt distH dh

        -- Bridge: subT(args, thmT y_h_r) = subT(args, codeFP) via d_h.
        bridge : Deriv (atomic (eqn (ap2 subT argsPair (ap1 thmT y_h_r))
                                     (ap2 subT argsPair codeFP)))
        bridge = congR subT argsPair d_h

        eBody_to_subT : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
                                            (ap2 subT argsPair codeFP)))
        eBody_to_subT = ruleTrans bodyEval bridge

        eSubT : Deriv (atomic (eqn (ap2 subT argsPair codeFP)
                                    (reify (codedSubst (code t) (code (var x))
                                                       (codeFormula P)))))
        eSubT = subTDef x (code t) (codeFormula P)
        eBody_to_codedSubst : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
          (reify (codedSubst (code t) (code (var x)) (codeFormula P)))))
        eBody_to_codedSubst = ruleTrans eBody_to_subT eSubT
        treeEq : Eq (codedSubst (code t) (code (var x)) (codeFormula P))
                    (codeFormula (substF x t P))
        treeEq = eqSym (codeCommutesFormula x t P)
    in eqSubst (\ T -> Deriv (atomic (eqn (ap2 body_ruleInst a bb) (reify T))))
               treeEq eBody_to_codedSubst

  -- thmTDispRuleInst : closed-form Theorem 11 dispatch (drops the
  -- inherited shape argument: under the new encoding the only
  -- distribution is through (Pair payVarX payT_t) whose Fst is closed).
  -- y_h' is retained as a no-op argument for backwards compat with
  -- callers (encodeRich and parDispRuleInst); the body simply ignores it.
  thmTDispRuleInst : (x : Nat) (t : Term) (P : Formula) (y_h : Tree)
                     (y_h' : Term) ->
    Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h'))) ->
    Deriv (atomic (eqn (ap1 thmT (reify y_h))
                       (reify (codeFormula P)))) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encRuleInst x t y_h)))
                       (reify (outRuleInst x t P))))
  thmTDispRuleInst x t P y_h y_h' shape_h d_h =
    let payVarX_ = reify (code (var x))
        payT_t_  = reify (code t)
        argsTree = nd (code (var x)) (code t)
        argsPair_ = reify argsTree
        y_h_r    = reify y_h
        payT     = reify (nd argsTree y_h)
        a        = ap2 Pair tagCode_ruleInst payT
        b        = ap2 Pair (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
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
        -- New layout: only ONE distribution needed.  Fst-shape on
        -- (reify argsTree) reduces via axFst to payVarX, and payVarX is
        -- definitionally  Pair (reify tagVar) (reify (natCode x)) , giving
        -- the Pair shape closed.
        argsShape : Deriv (atomic (eqn (ap1 Fst argsPair_)
                                        (ap2 Pair (reify tagVar)
                                                  (reify (natCode x)))))
        argsShape = axFst payVarX_ payT_t_
        distrib1 : Deriv (atomic (eqn (ap1 thmT payT)
                                      (ap2 Pair (ap1 thmT argsPair_) (ap1 thmT y_h_r))))
        distrib1 = thmTDistrib argsTree y_h (reify (natCode x)) argsShape
        distH = ruleTrans sndB_unfold distrib1
        be = body_ruleInst_eval x t P y_h b distH d_h
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans hh be))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Parametric variant of body_ruleInst_eval / thmTDispRuleInst.
  -- Takes the proof index as Term (xT) instead of Tree (y_h).
  --
  -- Used by step 4 of Theorem 14 (Goedel II's closure).  Caller
  -- supplies distHParam (parametric distribution of bb's Snd) and
  -- d_h (proof index's thmT-image).

  -- New layout: payT = Pair (Pair payVarX tT) xT  with the OPEN  xT
  -- (proof index) at outer Snd.
  body_ruleInst_eval_param :
    (n : Nat) (tT xT : Term) (bb : Term)
    (codeP fstPart sndPart : Term) ->
    -- distH: Snd bb = Pair (thmT (Pair payVarX tT)) (thmT xT) .
    Deriv (atomic (eqn (ap1 Snd bb)
                       (ap2 Pair (ap1 thmT (ap2 Pair (reify (code (var n))) tT))
                                 (ap1 thmT xT)))) ->
    Deriv (atomic (eqn (ap1 thmT xT) codeP)) ->
    -- NEW dh (load-bearing for body_ruleInst_v): codeP = Pair fstPart sndPart.
    Deriv (atomic (eqn codeP (ap2 Pair fstPart sndPart))) ->
    Deriv (atomic (eqn
      (ap2 body_ruleInst
            (ap2 Pair tagCode_ruleInst
                  (ap2 Pair (ap2 Pair (reify (code (var n))) tT) xT))
            bb)
      (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
  body_ruleInst_eval_param n tT xT bb codeP fstPart sndPart distH d_h dh =
    let payVarX : Term
        payVarX = reify (code (var n))
        argsPair : Term
        argsPair = ap2 Pair payVarX tT
        a : Term
        a = ap2 Pair tagCode_ruleInst (ap2 Pair argsPair xT)

        -- argsExt: Fst(Snd a) = argsPair.
        argsExt : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) argsPair))
        argsExt = ruleTrans (cong1 Fst (axSnd tagCode_ruleInst (ap2 Pair argsPair xT)))
                            (axFst argsPair xT)

        -- dhFinal: thmT xT = Pair fstPart sndPart (compose d_h with dh).
        dhFinal : Deriv (atomic (eqn (ap1 thmT xT) (ap2 Pair fstPart sndPart)))
        dhFinal = ruleTrans d_h dh

        -- Apply the verifying body's eval pass.
        bodyEval : Deriv (atomic (eqn (ap2 body_ruleInst a bb)
                                       (ap2 subT argsPair (ap1 thmT xT))))
        bodyEval = body_ruleInst_v_eval_pass a bb argsPair
                     (ap1 thmT argsPair) (ap1 thmT xT) fstPart sndPart
                     argsExt distH dhFinal

        -- Bridge: subT(args, thmT xT) = subT(args, codeP) via d_h.
        bridge : Deriv (atomic (eqn (ap2 subT argsPair (ap1 thmT xT))
                                     (ap2 subT argsPair codeP)))
        bridge = congR subT argsPair d_h
    in ruleTrans bodyEval bridge

  ------------------------------------------------------------------
  -- thmTDispRuleInst_param : full parametric dispatch for the sub-rule
  -- clause of th's defining equation (Guard Def 12 line 2).
  --
  -- NEW LAYOUT (refactor 2026-05-02): proof-index xT sits at OUTER Snd
  -- of the encoded payT, so distribution requires no shape on xT.
  --
  --   * n : Nat (variable index, closed; e.g. 1 for x_1)
  --   * tT xT : Term (substituted term, proof index — both open OK).
  --
  -- Output: Deriv (thmT (subProofEnc) = subT (varCode, tT) (thmT xT))
  --
  -- subProofEnc structure (NEW):
  --   ap2 Pair tagCode_ruleInst
  --     (ap2 Pair (ap2 Pair (reify (code (var n))) tT) xT)
  --
  -- The output subT-form, by sb's defining equation, equals
  --   sb (Pair tT (reify (natCode n))) (thmT xT)
  -- giving the asymmetric Theorem 13-style encoded equation
  -- "th(num x) = th(x)" parametric in the proof index xT,
  -- *without any shape obligation*.

  thmTDispRuleInst_param : (n : Nat) (tT xT : Term) (fstPart sndPart : Term) ->
    -- NEW dh (load-bearing for body_ruleInst_v): thmT xT = Pair fstPart sndPart .
    Deriv (atomic (eqn (ap1 thmT xT) (ap2 Pair fstPart sndPart))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleInst
                  (ap2 Pair (ap2 Pair (reify (code (var n))) tT) xT)))
      (ap2 subT (ap2 Pair (reify (code (var n))) tT) (ap1 thmT xT))))
  thmTDispRuleInst_param n tT xT fstPart sndPart dh =
    let payVarX : Term
        payVarX = reify (code (var n))
        argsPair : Term
        argsPair = ap2 Pair payVarX tT
        payT : Term
        payT = ap2 Pair argsPair xT
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

        -- distH derivation: parametric, ONE thmTDistrib_param application.
        -- Fst-shape on (Pair payVarX tT) is closed via axFst — payVarX is
        -- definitionally  Pair (reify tagVar) (reify (natCode n)) , so the
        -- Pair shape is immediate.  Independent of xT.
        sndB_unfold = axSnd (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)
        argsShape : Deriv (atomic (eqn (ap1 Fst argsPair)
                                        (ap2 Pair (reify tagVar)
                                                  (reify (natCode n)))))
        argsShape = axFst payVarX tT
        distrib1 = thmTDistrib_param argsPair xT
                                     {x' = reify tagVar}
                                     (reify (natCode n))
                                     argsShape
        distH = ruleTrans sndB_unfold distrib1

        -- d_h: thmT xT = thmT xT (refl).  Yields codeP = thmT xT.
        -- dh: caller-supplied Pair-shape witness on thmT xT.
        be = body_ruleInst_eval_param n tT xT b (ap1 thmT xT) fstPart sndPart
                                       distH (axRefl (ap1 thmT xT)) dh

    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans hh be))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- Lifted variant of body_ruleInst_eval_param using
  -- body_ruleInst_v_eval_pass_l.  innerL is the lifted inner-check
  -- witness  P imp (codeP = Pair fstPart sndPart) .

  body_ruleInst_eval_param_l :
    (P : Formula) (n : Nat) (tT xT : Term) (bb : Term)
    (codeP fstPart sndPart : Term) ->
    Deriv (P imp atomic (eqn (ap1 Snd bb)
                              (ap2 Pair (ap1 thmT (ap2 Pair (reify (code (var n))) tT))
                                        (ap1 thmT xT)))) ->
    Deriv (P imp atomic (eqn (ap1 thmT xT) codeP)) ->
    Deriv (P imp atomic (eqn codeP (ap2 Pair fstPart sndPart))) ->
    Deriv (P imp atomic (eqn
      (ap2 body_ruleInst
            (ap2 Pair tagCode_ruleInst
                  (ap2 Pair (ap2 Pair (reify (code (var n))) tT) xT))
            bb)
      (ap2 subT (ap2 Pair (reify (code (var n))) tT) codeP)))
  body_ruleInst_eval_param_l P n tT xT bb codeP fstPart sndPart distHL d_hL dhL =
    let payVarX : Term
        payVarX = reify (code (var n))
        argsPair : Term
        argsPair = ap2 Pair payVarX tT
        a : Term
        a = ap2 Pair tagCode_ruleInst (ap2 Pair argsPair xT)

        -- argsExt: closed Fst(Snd a) = argsPair, lifted to P.
        argsExt0 : Deriv (atomic (eqn (ap1 Fst (ap1 Snd a)) argsPair))
        argsExt0 = ruleTrans (cong1 Fst (axSnd tagCode_ruleInst (ap2 Pair argsPair xT)))
                             (axFst argsPair xT)
        argsExtL : Deriv (P imp atomic (eqn (ap1 Fst (ap1 Snd a)) argsPair))
        argsExtL = liftAxiom P argsExt0

        -- dhFinalL: thmT xT = Pair fstPart sndPart, lifted under P.
        dhFinalL : Deriv (P imp atomic (eqn (ap1 thmT xT) (ap2 Pair fstPart sndPart)))
        dhFinalL = liftedRuleTrans P (ap1 thmT xT) codeP (ap2 Pair fstPart sndPart)
                     d_hL dhL

        -- Apply the lifted verifying body's eval pass.
        bodyEvalL : Deriv (P imp atomic (eqn (ap2 body_ruleInst a bb)
                                              (ap2 subT argsPair (ap1 thmT xT))))
        bodyEvalL = body_ruleInst_v_eval_pass_l P a bb argsPair
                      (ap1 thmT argsPair) (ap1 thmT xT) fstPart sndPart
                      argsExtL distHL dhFinalL

        -- Bridge: subT(args, thmT xT) = subT(args, codeP) via lifted d_h.
        bridgeL : Deriv (P imp atomic (eqn (ap2 subT argsPair (ap1 thmT xT))
                                            (ap2 subT argsPair codeP)))
        bridgeL = liftedCongR P subT (ap1 thmT xT) codeP argsPair d_hL
    in liftedRuleTrans P (ap2 body_ruleInst a bb)
         (ap2 subT argsPair (ap1 thmT xT)) (ap2 subT argsPair codeP)
         bodyEvalL bridgeL

  ------------------------------------------------------------------
  -- thmTDispRuleInst_param_l : lifted variant of thmTDispRuleInst_param.
  --
  -- Mirrors thmTDispMp_param_l: split the unlifted dispatcher prefix
  -- (tag-skip cascade) from the lifted body-eval call.  The new innerL
  -- hypothesis  (P imp atomic (eqn (thmT xT) (Pair fstPart sndPart)))
  -- threads through  body_ruleInst_eval_param_l .

  thmTDispRuleInst_param_l : (P : Formula)
    (n : Nat) (tT xT : Term) (fstPart sndPart : Term) ->
    Deriv (P imp atomic (eqn (ap1 thmT xT) (ap2 Pair fstPart sndPart))) ->
    Deriv (P imp atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleInst
                  (ap2 Pair (ap2 Pair (reify (code (var n))) tT) xT)))
      (ap2 subT (ap2 Pair (reify (code (var n))) tT) (ap1 thmT xT))))
  thmTDispRuleInst_param_l P n tT xT fstPart sndPart innerL =
    let payVarX : Term
        payVarX = reify (code (var n))
        argsPair : Term
        argsPair = ap2 Pair payVarX tT
        payT : Term
        payT = ap2 Pair argsPair xT
        a : Term
        a = ap2 Pair tagCode_ruleInst payT
        b : Term
        b = ap2 Pair (ap1 thmT tagCode_ruleInst) (ap1 thmT payT)

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

        prefixClosed : Deriv (atomic (eqn (ap1 thmT a) (ap2 body_ruleInst a b)))
        prefixClosed =
          ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
          (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
          (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
          (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
          (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
          (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
          (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
          (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
          (ruleTrans s36 (ruleTrans s37 hh)))))))))))))))))))))))))))))))))
        prefixL : Deriv (P imp atomic (eqn (ap1 thmT a) (ap2 body_ruleInst a b)))
        prefixL = liftAxiom P prefixClosed

        sndBunfoldL : Deriv (P imp atomic (eqn (ap1 Snd b) (ap1 thmT payT)))
        sndBunfoldL = liftAxiom P (axSnd (ap1 thmT tagCode_ruleInst) (ap1 thmT payT))

        argsShape0 : Deriv (atomic (eqn (ap1 Fst argsPair)
                                          (ap2 Pair (reify tagVar)
                                                    (reify (natCode n)))))
        argsShape0 = axFst payVarX tT
        argsShapeL : Deriv (P imp atomic (eqn (ap1 Fst argsPair)
                                                (ap2 Pair (reify tagVar)
                                                          (reify (natCode n)))))
        argsShapeL = liftAxiom P argsShape0

        distribL : Deriv (P imp atomic (eqn (ap1 thmT payT)
                                              (ap2 Pair (ap1 thmT argsPair) (ap1 thmT xT))))
        distribL = thmTDistrib_param_l P argsPair xT
                                       {x' = reify tagVar}
                                       (reify (natCode n))
                                       argsShapeL

        distHL : Deriv (P imp atomic (eqn (ap1 Snd b)
                                            (ap2 Pair (ap1 thmT argsPair) (ap1 thmT xT))))
        distHL = liftedRuleTrans P (ap1 Snd b) (ap1 thmT payT)
                   (ap2 Pair (ap1 thmT argsPair) (ap1 thmT xT))
                   sndBunfoldL distribL

        d_hReflL : Deriv (P imp atomic (eqn (ap1 thmT xT) (ap1 thmT xT)))
        d_hReflL = liftAxiom P (axRefl (ap1 thmT xT))

        beL : Deriv (P imp atomic (eqn (ap2 body_ruleInst a b)
                                        (ap2 subT argsPair (ap1 thmT xT))))
        beL = body_ruleInst_eval_param_l P n tT xT b (ap1 thmT xT)
                fstPart sndPart distHL d_hReflL innerL
    in liftedRuleTrans P (ap1 thmT a) (ap2 body_ruleInst a b)
         (ap2 subT argsPair (ap1 thmT xT))
         prefixL beL

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

        eARGS : Deriv (atomic (eqn (ap2 RI2Proto.argsExtractor a bb) argsPair))
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

        ePostUnf : Deriv (atomic (eqn (ap2 RI2Proto.codepExtractor a bb)
          (ap1 (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) (ap2 Pair a bb))))
        ePostUnf = axPost (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) Pair a bb

        eUnf1 : Deriv (atomic (eqn
          (ap1 (Comp (Comp Fst Snd) (Comp Snd (Comp Snd Snd))) (ap2 Pair a bb))
          (ap1 (Comp Fst Snd) (ap1 (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)))))
        eUnf1 = axComp (Comp Fst Snd) (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)

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

        eOuter : Deriv (atomic (eqn
          (ap1 (Comp Fst Snd) (ap1 (Comp Snd (Comp Snd Snd)) (ap2 Pair a bb)))
          (ap1 (Comp Fst Snd) (ap1 Snd (ap1 Snd bb)))))
        eOuter = cong1 (Comp Fst Snd) eUnf2_to_SndSndbb

        ePostBase : Deriv (atomic (eqn
          (ap2 RI2Proto.codepExtractor a bb)
          (ap1 (Comp Fst Snd) (ap1 Snd (ap1 Snd bb)))))
        ePostBase = ruleTrans ePostUnf (ruleTrans eUnf1 eOuter)

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

        eCODEP_to_tjH : Deriv (atomic (eqn (ap2 RI2Proto.codepExtractor a bb) tjH))
        eCODEP_to_tjH = ruleTrans ePostBase (ruleTrans ePushFstSnd eFinalToTjH)

        eCODEP : Deriv (atomic (eqn (ap2 RI2Proto.codepExtractor a bb) codeFP))
        eCODEP = ruleTrans eCODEP_to_tjH d_h

        -- Pair-shape of codeFP via codeFormulaPairShape.
        shapeP = codeFormulaPairShape P
        fp : Term
        fp = fst shapeP
        sp : Term
        sp = fst (snd shapeP)
        reifyPairEq : Deriv (atomic (eqn codeFP (ap2 Pair fp sp)))
        reifyPairEq = snd (snd shapeP)

        -- Apply the verifying body's eval pass.
        bodyEval : Deriv (atomic (eqn (ap2 body_ruleInst2 a bb)
                                       (ap2 subT2 argsPair codeFP)))
        bodyEval = body_ruleInst2_v_eval_pass a bb argsPair codeFP fp sp
                     eARGS eCODEP reifyPairEq

        eSubT2 : Deriv (atomic (eqn (ap2 subT2 argsPair codeFP)
          (reify (codedSubst2 (code tA) (code tB)
                              (code (var xA)) (code (var xB))
                              (codeFormula P)))))
        eSubT2 = subTDef2 xA xB (code tA) (code tB) (codeFormula P)

        eBody_to_codedSubst2 : Deriv (atomic (eqn (ap2 body_ruleInst2 a bb)
          (reify (codedSubst2 (code tA) (code tB)
                              (code (var xA)) (code (var xB))
                              (codeFormula P)))))
        eBody_to_codedSubst2 = ruleTrans bodyEval eSubT2

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
        hh   = hitAtTag  (natCode tagRuleInst2)   tagCode_ruleInst2 payT b body_ruleInst2   next_ruleInst2
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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- thmTDispAxTreeRecLf : dispatcher for the unified tree-recursor
  -- leaf axiom.  44 skipAtTag steps + 1 hitAtTag.

  thmTDispAxTreeRecLf : (f : Fun1) (s : Fun2) (p : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxTreeRecLf f s p)))
                       (reify (outAxTreeRecLf f s p))))
  thmTDispAxTreeRecLf f s p =
    let payT = reify (nd (codeF1 f) (nd (codeF2 s) (code p)))
        a    = ap2 Pair tagCode_axTreeRecLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeRecLf) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleIndBT2 payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axTreeRecLf payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxTreeRecLf refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axTreeRecLf payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxTreeRecLf refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axTreeRecLf payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxTreeRecLf refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axTreeRecLf payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxTreeRecLf refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axTreeRecLf payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxTreeRecLf refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axTreeRecLf payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxTreeRecLf refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axTreeRecLf payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxTreeRecLf refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axTreeRecLf payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxTreeRecLf refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axTreeRecLf payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxTreeRecLf refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axTreeRecLf payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxTreeRecLf refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axTreeRecLf payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxTreeRecLf refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axTreeRecLf payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxTreeRecLf refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axTreeRecLf payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxTreeRecLf refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axTreeRecLf payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxTreeRecLf refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axTreeRecLf payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxTreeRecLf refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axTreeRecLf payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxTreeRecLf refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axTreeRecLf payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxTreeRecLf refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axTreeRecLf payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxTreeRecLf refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axTreeRecLf payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxTreeRecLf refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axTreeRecLf payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxTreeRecLf refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axTreeRecLf payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxTreeRecLf refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axTreeRecLf payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxTreeRecLf refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axTreeRecLf payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxTreeRecLf refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axTreeRecLf payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxTreeRecLf refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axTreeRecLf payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxTreeRecLf refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axTreeRecLf payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxTreeRecLf refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axTreeRecLf payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxTreeRecLf refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axTreeRecLf payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxTreeRecLf refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axTreeRecLf payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxTreeRecLf refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axTreeRecLf payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxTreeRecLf refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axTreeRecLf payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxTreeRecLf refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axTreeRecLf payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxTreeRecLf refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axTreeRecLf payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxTreeRecLf refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axTreeRecLf payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxTreeRecLf refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axTreeRecLf payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxTreeRecLf refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axTreeRecLf payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxTreeRecLf refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axTreeRecLf payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxTreeRecLf refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_axTreeRecLf payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagAxTreeRecLf refl)
        s43  = skipAtTag (natCode tagAxIfLfNL)    tagCode_axTreeRecLf payT b body_axIfLfNL    next_axIfLfNL
                  (teqDiff tagAxIfLfNL    tagAxTreeRecLf refl)
        s44  = skipAtTag (natCode tagRuleInst2)   tagCode_axTreeRecLf payT b body_ruleInst2   next_ruleInst2
                  (teqDiff tagRuleInst2   tagAxTreeRecLf refl)
        hh   = hitAtTag  (natCode tagAxTreeRecLf) tagCode_axTreeRecLf payT b body_axTreeRecLf next_axTreeRecLf
                  (teqEq tagAxTreeRecLf)
        be   = body_axTreeRecLf_eval f s p b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans s44 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- thmTDispAxTreeRecNd : dispatcher for the unified tree-recursor
  -- step axiom.  45 skipAtTag steps + 1 hitAtTag.

  thmTDispAxTreeRecNd : (f : Fun1) (s : Fun2) (p a' b' : Term) ->
    Deriv (atomic (eqn (ap1 thmT (reify (encAxTreeRecNd f s p a' b')))
                       (reify (outAxTreeRecNd f s p a' b'))))
  thmTDispAxTreeRecNd f s p a' b' =
    let payT = reify (nd (codeF1 f)
                         (nd (codeF2 s)
                             (nd (code p)
                                 (nd (code a') (code b')))))
        a    = ap2 Pair tagCode_axTreeRecNd payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeRecNd) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeRecLf payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axTreeRecNd payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxTreeRecNd refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axTreeRecNd payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxTreeRecNd refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axTreeRecNd payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxTreeRecNd refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axTreeRecNd payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxTreeRecNd refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axTreeRecNd payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxTreeRecNd refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axTreeRecNd payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxTreeRecNd refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axTreeRecNd payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxTreeRecNd refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axTreeRecNd payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxTreeRecNd refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axTreeRecNd payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxTreeRecNd refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axTreeRecNd payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxTreeRecNd refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axTreeRecNd payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxTreeRecNd refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axTreeRecNd payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxTreeRecNd refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axTreeRecNd payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxTreeRecNd refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axTreeRecNd payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxTreeRecNd refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axTreeRecNd payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxTreeRecNd refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axTreeRecNd payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxTreeRecNd refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axTreeRecNd payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxTreeRecNd refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axTreeRecNd payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxTreeRecNd refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axTreeRecNd payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxTreeRecNd refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axTreeRecNd payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxTreeRecNd refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axTreeRecNd payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxTreeRecNd refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axTreeRecNd payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxTreeRecNd refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axTreeRecNd payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxTreeRecNd refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axTreeRecNd payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxTreeRecNd refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axTreeRecNd payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxTreeRecNd refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axTreeRecNd payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxTreeRecNd refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axTreeRecNd payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxTreeRecNd refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axTreeRecNd payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxTreeRecNd refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axTreeRecNd payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxTreeRecNd refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axTreeRecNd payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxTreeRecNd refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axTreeRecNd payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxTreeRecNd refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axTreeRecNd payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxTreeRecNd refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axTreeRecNd payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxTreeRecNd refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axTreeRecNd payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxTreeRecNd refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axTreeRecNd payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxTreeRecNd refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axTreeRecNd payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxTreeRecNd refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axTreeRecNd payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxTreeRecNd refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_axTreeRecNd payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagAxTreeRecNd refl)
        s43  = skipAtTag (natCode tagAxIfLfNL)    tagCode_axTreeRecNd payT b body_axIfLfNL    next_axIfLfNL
                  (teqDiff tagAxIfLfNL    tagAxTreeRecNd refl)
        s44  = skipAtTag (natCode tagRuleInst2)   tagCode_axTreeRecNd payT b body_ruleInst2   next_ruleInst2
                  (teqDiff tagRuleInst2   tagAxTreeRecNd refl)
        s45  = skipAtTag (natCode tagAxTreeRecLf) tagCode_axTreeRecNd payT b body_axTreeRecLf next_axTreeRecLf
                  (teqDiff tagAxTreeRecLf tagAxTreeRecNd refl)
        hh   = hitAtTag  (natCode tagAxTreeRecNd) tagCode_axTreeRecNd payT b body_axTreeRecNd fbBody
                  (teqEq tagAxTreeRecNd)
        be   = body_axTreeRecNd_eval f s p a' b' b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans s44 (ruleTrans s45 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- thmTDispAxTreeRecLf_param : parametric variant of
  -- thmTDispAxTreeRecLf.  Takes Term substituents fT, sT, pT directly,
  -- producing the reduced-Pair RHS (no  reify (outAxTreeRecLf ...)
  -- meta-reify).  Used by Theorem 12 / Thm12.Param.AxTreeRecLf.

  thmTDispAxTreeRecLf_param : (fT sT pT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axTreeRecLf (ap2 Pair fT (ap2 Pair sT pT))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                              (ap2 Pair fT sT))
                    (ap2 Pair pT O)))
        (ap2 Pair (reify tagAp1) (ap2 Pair fT pT)))))
  thmTDispAxTreeRecLf_param fT sT pT =
    let payT = ap2 Pair fT (ap2 Pair sT pT)
        a    = ap2 Pair tagCode_axTreeRecLf payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeRecLf) (ap1 thmT payT)
        e1   = dispatchOpens tagRuleIndBT2 payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axTreeRecLf payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxTreeRecLf refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axTreeRecLf payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxTreeRecLf refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axTreeRecLf payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxTreeRecLf refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axTreeRecLf payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxTreeRecLf refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axTreeRecLf payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxTreeRecLf refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axTreeRecLf payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxTreeRecLf refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axTreeRecLf payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxTreeRecLf refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axTreeRecLf payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxTreeRecLf refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axTreeRecLf payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxTreeRecLf refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axTreeRecLf payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxTreeRecLf refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axTreeRecLf payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxTreeRecLf refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axTreeRecLf payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxTreeRecLf refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axTreeRecLf payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxTreeRecLf refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axTreeRecLf payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxTreeRecLf refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axTreeRecLf payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxTreeRecLf refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axTreeRecLf payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxTreeRecLf refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axTreeRecLf payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxTreeRecLf refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axTreeRecLf payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxTreeRecLf refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axTreeRecLf payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxTreeRecLf refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axTreeRecLf payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxTreeRecLf refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axTreeRecLf payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxTreeRecLf refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axTreeRecLf payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxTreeRecLf refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axTreeRecLf payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxTreeRecLf refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axTreeRecLf payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxTreeRecLf refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axTreeRecLf payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxTreeRecLf refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axTreeRecLf payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxTreeRecLf refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axTreeRecLf payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxTreeRecLf refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axTreeRecLf payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxTreeRecLf refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axTreeRecLf payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxTreeRecLf refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axTreeRecLf payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxTreeRecLf refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axTreeRecLf payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxTreeRecLf refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axTreeRecLf payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxTreeRecLf refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axTreeRecLf payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxTreeRecLf refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axTreeRecLf payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxTreeRecLf refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axTreeRecLf payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxTreeRecLf refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axTreeRecLf payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxTreeRecLf refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axTreeRecLf payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxTreeRecLf refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_axTreeRecLf payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagAxTreeRecLf refl)
        s43  = skipAtTag (natCode tagAxIfLfNL)    tagCode_axTreeRecLf payT b body_axIfLfNL    next_axIfLfNL
                  (teqDiff tagAxIfLfNL    tagAxTreeRecLf refl)
        s44  = skipAtTag (natCode tagRuleInst2)   tagCode_axTreeRecLf payT b body_ruleInst2   next_ruleInst2
                  (teqDiff tagRuleInst2   tagAxTreeRecLf refl)
        hh   = hitAtTag  (natCode tagAxTreeRecLf) tagCode_axTreeRecLf payT b body_axTreeRecLf next_axTreeRecLf
                  (teqEq tagAxTreeRecLf)
        be   = body_axTreeRecLf_eval_param fT sT pT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans s44 (ruleTrans hh be)))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- thmTDispAxTreeRecNd_param : parametric variant of
  -- thmTDispAxTreeRecNd.  Takes Term substituents fT, sT, pT, aT, bT
  -- directly, producing the reduced-Pair RHS.

  thmTDispAxTreeRecNd_param : (fT sT pT aT bT : Term) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_axTreeRecNd
                   (ap2 Pair fT (ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT))))))
      (ap2 Pair
        (ap2 Pair (reify tagAp2)
          (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                              (ap2 Pair fT sT))
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
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                          (ap2 Pair fT sT))
                                (ap2 Pair pT aT)))
                    (ap2 Pair (reify tagAp2)
                      (ap2 Pair (ap2 Pair (reify (leftT (codeF2 (treeRec I IfLf))))
                                          (ap2 Pair fT sT))
                                (ap2 Pair pT bT))))))))))))
  thmTDispAxTreeRecNd_param fT sT pT aT bT =
    let payT = ap2 Pair fT (ap2 Pair sT (ap2 Pair pT (ap2 Pair aT bT)))
        a    = ap2 Pair tagCode_axTreeRecNd payT
        b    = ap2 Pair (ap1 thmT tagCode_axTreeRecNd) (ap1 thmT payT)
        e1   = dispatchOpens tagAxTreeRecLf payT
        s1   = skipAtTag (natCode tagAxI)         tagCode_axTreeRecNd payT b body_axI         next_axI
                  (teqDiff tagAxI         tagAxTreeRecNd refl)
        s2   = skipAtTag (natCode tagAxFst)       tagCode_axTreeRecNd payT b body_axFst       next_axFst
                  (teqDiff tagAxFst       tagAxTreeRecNd refl)
        s3   = skipAtTag (natCode tagAxSnd)       tagCode_axTreeRecNd payT b body_axSnd       next_axSnd
                  (teqDiff tagAxSnd       tagAxTreeRecNd refl)
        s4   = skipAtTag (natCode tagAxConst)     tagCode_axTreeRecNd payT b body_axConst     next_axConst
                  (teqDiff tagAxConst     tagAxTreeRecNd refl)
        s5   = skipAtTag (natCode tagAxComp)      tagCode_axTreeRecNd payT b body_axComp      next_axComp
                  (teqDiff tagAxComp      tagAxTreeRecNd refl)
        s6   = skipAtTag (natCode tagAxComp2)     tagCode_axTreeRecNd payT b body_axComp2     next_axComp2
                  (teqDiff tagAxComp2     tagAxTreeRecNd refl)
        s7   = skipAtTag (natCode tagAxLift)      tagCode_axTreeRecNd payT b body_axLift      next_axLift
                  (teqDiff tagAxLift      tagAxTreeRecNd refl)
        s8   = skipAtTag (natCode tagAxPost)      tagCode_axTreeRecNd payT b body_axPost      next_axPost
                  (teqDiff tagAxPost      tagAxTreeRecNd refl)
        s9   = skipAtTag (natCode tagAxFan)       tagCode_axTreeRecNd payT b body_axFan       next_axFan
                  (teqDiff tagAxFan       tagAxTreeRecNd refl)
        s10  = skipAtTag (natCode tagAxKT)        tagCode_axTreeRecNd payT b body_axZ         next_axKT
                  (teqDiff tagAxKT        tagAxTreeRecNd refl)
        s15  = skipAtTag (natCode tagAxIfLfL)     tagCode_axTreeRecNd payT b body_axIfLfL     next_axIfLfL
                  (teqDiff tagAxIfLfL     tagAxTreeRecNd refl)
        s16  = skipAtTag (natCode tagAxIfLfN)     tagCode_axTreeRecNd payT b body_axIfLfN     next_axIfLfN
                  (teqDiff tagAxIfLfN     tagAxTreeRecNd refl)
        s17  = skipAtTag (natCode tagAxTreeEqLL)  tagCode_axTreeRecNd payT b body_axTreeEqLL  next_axTreeEqLL
                  (teqDiff tagAxTreeEqLL  tagAxTreeRecNd refl)
        s18  = skipAtTag (natCode tagAxTreeEqLN)  tagCode_axTreeRecNd payT b body_axTreeEqLN  next_axTreeEqLN
                  (teqDiff tagAxTreeEqLN  tagAxTreeRecNd refl)
        s19  = skipAtTag (natCode tagAxTreeEqNL)  tagCode_axTreeRecNd payT b body_axTreeEqNL  next_axTreeEqNL
                  (teqDiff tagAxTreeEqNL  tagAxTreeRecNd refl)
        s20  = skipAtTag (natCode tagAxTreeEqNN)  tagCode_axTreeRecNd payT b body_axTreeEqNN  next_axTreeEqNN
                  (teqDiff tagAxTreeEqNN  tagAxTreeRecNd refl)
        s21  = skipAtTag (natCode tagAxGoodstein) tagCode_axTreeRecNd payT b body_axGoodstein next_axGoodstein
                  (teqDiff tagAxGoodstein tagAxTreeRecNd refl)
        s22  = skipAtTag (natCode tagAxRefl)      tagCode_axTreeRecNd payT b body_axRefl      next_axRefl
                  (teqDiff tagAxRefl      tagAxTreeRecNd refl)
        s23  = skipAtTag (natCode tagRuleSym)     tagCode_axTreeRecNd payT b body_ruleSym     next_ruleSym
                  (teqDiff tagRuleSym     tagAxTreeRecNd refl)
        s24  = skipAtTag (natCode tagRuleTrans)   tagCode_axTreeRecNd payT b body_ruleTrans   next_ruleTrans
                  (teqDiff tagRuleTrans   tagAxTreeRecNd refl)
        s25  = skipAtTag (natCode tagCong1)       tagCode_axTreeRecNd payT b body_cong1       next_cong1
                  (teqDiff tagCong1       tagAxTreeRecNd refl)
        s26  = skipAtTag (natCode tagCongL)       tagCode_axTreeRecNd payT b body_congL       next_congL
                  (teqDiff tagCongL       tagAxTreeRecNd refl)
        s27  = skipAtTag (natCode tagCongR)       tagCode_axTreeRecNd payT b body_congR       next_congR
                  (teqDiff tagCongR       tagAxTreeRecNd refl)
        s28  = skipAtTag (natCode tagAxEqTrans)   tagCode_axTreeRecNd payT b body_axEqTrans   next_axEqTrans
                  (teqDiff tagAxEqTrans   tagAxTreeRecNd refl)
        s29  = skipAtTag (natCode tagAxEqCong1)   tagCode_axTreeRecNd payT b body_axEqCong1   next_axEqCong1
                  (teqDiff tagAxEqCong1   tagAxTreeRecNd refl)
        s30  = skipAtTag (natCode tagAxEqCongL)   tagCode_axTreeRecNd payT b body_axEqCongL   next_axEqCongL
                  (teqDiff tagAxEqCongL   tagAxTreeRecNd refl)
        s31  = skipAtTag (natCode tagAxEqCongR)   tagCode_axTreeRecNd payT b body_axEqCongR   next_axEqCongR
                  (teqDiff tagAxEqCongR   tagAxTreeRecNd refl)
        s32  = skipAtTag (natCode tagAxK)         tagCode_axTreeRecNd payT b body_axK         next_axK
                  (teqDiff tagAxK         tagAxTreeRecNd refl)
        s33  = skipAtTag (natCode tagAxS)         tagCode_axTreeRecNd payT b body_axS         next_axS
                  (teqDiff tagAxS         tagAxTreeRecNd refl)
        s34  = skipAtTag (natCode tagAxNeg)       tagCode_axTreeRecNd payT b body_axNeg       next_axNeg
                  (teqDiff tagAxNeg       tagAxTreeRecNd refl)
        s35  = skipAtTag (natCode tagAxExFalso)   tagCode_axTreeRecNd payT b body_axExFalso   next_axExFalso
                  (teqDiff tagAxExFalso   tagAxTreeRecNd refl)
        s36  = skipAtTag (natCode tagAxContrapos) tagCode_axTreeRecNd payT b body_axContrapos next_axContrapos
                  (teqDiff tagAxContrapos tagAxTreeRecNd refl)
        s37  = skipAtTag (natCode tagMp)          tagCode_axTreeRecNd payT b body_mp          next_mp
                  (teqDiff tagMp          tagAxTreeRecNd refl)
        s38  = skipAtTag (natCode tagRuleInst)    tagCode_axTreeRecNd payT b body_ruleInst    next_ruleInst
                  (teqDiff tagRuleInst    tagAxTreeRecNd refl)
        s39  = skipAtTag (natCode tagRuleIndBT)   tagCode_axTreeRecNd payT b body_ruleIndBT   next_ruleIndBT
                  (teqDiff tagRuleIndBT   tagAxTreeRecNd refl)
        s40  = skipAtTag (natCode tagAxFstLf)     tagCode_axTreeRecNd payT b body_axFstLf     next_axFstLf
                  (teqDiff tagAxFstLf     tagAxTreeRecNd refl)
        s41  = skipAtTag (natCode tagAxSndLf)     tagCode_axTreeRecNd payT b body_axSndLf     next_axSndLf
                  (teqDiff tagAxSndLf     tagAxTreeRecNd refl)
        s42  = skipAtTag (natCode tagAxIfLfLL)    tagCode_axTreeRecNd payT b body_axIfLfLL    next_axIfLfLL
                  (teqDiff tagAxIfLfLL    tagAxTreeRecNd refl)
        s43  = skipAtTag (natCode tagAxIfLfNL)    tagCode_axTreeRecNd payT b body_axIfLfNL    next_axIfLfNL
                  (teqDiff tagAxIfLfNL    tagAxTreeRecNd refl)
        s44  = skipAtTag (natCode tagRuleInst2)   tagCode_axTreeRecNd payT b body_ruleInst2   next_ruleInst2
                  (teqDiff tagRuleInst2   tagAxTreeRecNd refl)
        s45  = skipAtTag (natCode tagAxTreeRecLf) tagCode_axTreeRecNd payT b body_axTreeRecLf next_axTreeRecLf
                  (teqDiff tagAxTreeRecLf tagAxTreeRecNd refl)
        hh   = hitAtTag  (natCode tagAxTreeRecNd) tagCode_axTreeRecNd payT b body_axTreeRecNd fbBody
                  (teqEq tagAxTreeRecNd)
        be   = body_axTreeRecNd_eval_param fT sT pT aT bT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans s44 (ruleTrans s45 (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))))

  ------------------------------------------------------------------
  -- body_ruleInst2_eval_param: parametric variant of body_ruleInst2_eval.
  -- Takes Term substituents tA, tB and Term proof index xT.  Returns
  -- the subT2-form (without applying subTDef2 + codeCommutes2), so
  -- callers can plug in their own concrete reductions.

  body_ruleInst2_eval_param :
    (nA nB : Nat) (tA tB xT : Term) (bb : Term) (codeP fp sp : Term) ->
    Deriv (atomic (eqn (ap1 Snd bb)
      (ap2 Pair (ap1 thmT (reify (code (var nA))))
       (ap2 Pair (ap1 thmT (reify (code (var nB))))
        (ap2 Pair (ap1 thmT xT)
                  (ap1 thmT (ap2 Pair tA tB))))))) ->
    Deriv (atomic (eqn (ap1 thmT xT) codeP)) ->
    Deriv (atomic (eqn codeP (ap2 Pair fp sp))) ->
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
  body_ruleInst2_eval_param nA nB tA tB xT bb codeP fp sp distH d_h codePShape =
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

        eARGS : Deriv (atomic (eqn (ap2 RI2Proto.argsExtractor a bb) argsPair))
        eARGS = pairOfFan_eval
          (Fan (Lift (Comp Fst Snd))
               (Lift (Comp Fst (Comp Snd (Comp Snd (Comp Snd Snd)))))
               Pair)
          (Fan (Lift (Comp Fst (Comp Snd Snd)))
               (Lift (Comp Snd (Comp Snd (Comp Snd (Comp Snd Snd)))))
               Pair)
          a bb innerA innerB eInnerA eInnerB

        ePostUnf : Deriv (atomic (eqn (ap2 RI2Proto.codepExtractor a bb)
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
          (ap2 RI2Proto.codepExtractor a bb)
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
        eCODEP : Deriv (atomic (eqn (ap2 RI2Proto.codepExtractor a bb) codeP))
        eCODEP = ruleTrans eCODEP_to_tjH d_h
    in body_ruleInst2_v_eval_pass a bb argsPair codeP fp sp eARGS eCODEP codePShape

  ------------------------------------------------------------------
  -- thmTDispRuleInst2_param: full parametric dispatch for the
  -- simultaneous double-substitution proof code.  Mirrors
  -- thmTDispRuleInst_param (single substitution) but takes TWO
  -- runtime substituent Terms.

  thmTDispRuleInst2_param : (nA nB : Nat) (tA tB xT : Term)
    (xShape : Sigma Term (\ y' -> Sigma Term (\ x' ->
       Deriv (atomic (eqn (ap1 Fst xT) (ap2 Pair x' y'))))))
    (codePfp codePsp : Term)
    (codePShape : Deriv (atomic (eqn (ap1 thmT xT) (ap2 Pair codePfp codePsp)))) ->
    Deriv (atomic (eqn
      (ap1 thmT (ap2 Pair tagCode_ruleInst2
                  (ap2 Pair (reify (code (var nA)))
                    (ap2 Pair (reify (code (var nB)))
                      (ap2 Pair xT (ap2 Pair tA tB))))))
      (ap2 subT2 (ap2 Pair (ap2 Pair (reify (code (var nA))) tA)
                            (ap2 Pair (reify (code (var nB))) tB))
                  (ap1 thmT xT))))
  thmTDispRuleInst2_param nA nB tA tB xT xShape codePfp codePsp codePShape =
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
        hh   = hitAtTag  (natCode tagRuleInst2)   tagCode_ruleInst2 payT b body_ruleInst2   next_ruleInst2
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
                                        codePfp codePsp
                                        distH (axRefl (ap1 thmT xT)) codePShape

    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans s20 (ruleTrans s21 (ruleTrans s22 (ruleTrans s23
       (ruleTrans s24 (ruleTrans s25 (ruleTrans s26 (ruleTrans s27
       (ruleTrans s28 (ruleTrans s29 (ruleTrans s30 (ruleTrans s31
       (ruleTrans s32 (ruleTrans s33 (ruleTrans s34 (ruleTrans s35
       (ruleTrans s36 (ruleTrans s37 (ruleTrans s38 (ruleTrans s39
       (ruleTrans s40 (ruleTrans s41 (ruleTrans s42 (ruleTrans s43
       (ruleTrans hh be))))))))))))))))))))))))))))))))))))))))

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
        s15  = skipAtTag (natCode tagAxIfLfL)   tagCode_axTreeEqLL payT b body_axIfLfL   next_axIfLfL
                  (teqDiff tagAxIfLfL   tagAxTreeEqLL refl)
        s16  = skipAtTag (natCode tagAxIfLfN)   tagCode_axTreeEqLL payT b body_axIfLfN   next_axIfLfN
                  (teqDiff tagAxIfLfN   tagAxTreeEqLL refl)
        hh   = hitAtTag  (natCode tagAxTreeEqLL) tagCode_axTreeEqLL payT b body_axTreeEqLL next_axTreeEqLL
                  (teqEq tagAxTreeEqLL)
        be   = body_axTreeEqLL_eval_param payT b
    in ruleTrans e1 (ruleTrans s1 (ruleTrans s2 (ruleTrans s3
       (ruleTrans s4 (ruleTrans s5 (ruleTrans s6 (ruleTrans s7
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans hh be)))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans hh be))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans hh be)))))))))))))))

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
       (ruleTrans s8 (ruleTrans s9 (ruleTrans s10 (ruleTrans s15
       (ruleTrans s16 (ruleTrans s17 (ruleTrans s18 (ruleTrans s19
       (ruleTrans hh be))))))))))))))))


  -- thmTDispAxRecLf_param / thmTDispAxRecNd_param removed:
  -- axRecLf and axRecNd demoted to derived lemmas (BRA/Deriv.agda).



------------------------------------------------------------------------
-- WithDispatch : module parameterised by the 30 dispatch lemmas not
-- proved in this session.  Sessions D-F instantiate.
--
-- 19 non-recursive (axiomatic):
--   axRecLf  axRecNd
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

  -- {P : Formula} is implicit and inferred from the Deriv constructor.
  -- Avoids dot patterns (`.(formula)`) — keeps the file fancy-feature-free.
  -- See BRA/ARCHITECTURE-FINDINGS.md for the principle.
  encodeRich : {P : Formula} -> Deriv P ->
    Sigma Tree (\ y ->
      Sigma Term (\ y' ->
        Sigma (Deriv (atomic (eqn (ap1 Fst (reify y)) (ap2 Pair O y'))))
              (\ _ -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                          (reify (codeFormula P)))))))

  -- Recursive / function-valued-index clauses come FIRST.
  -- This redirects Agda's coverage check away from the
  -- SplitError.UnificationStuck triggered by  ruleInst 's
  --  substF x t P  return-type-index when many concrete-index
  -- axiom clauses follow.  See BRA/ARCHITECTURE-FINDINGS.md.
  encodeRich (mp {P = P} {Q = Q} pf1 pf2) =
    let r1 = encodeRich pf1
        r2 = encodeRich pf2
        y1 = fst r1
        y1' = fst (snd r1)
        shape1 = fst (snd (snd r1))
        d1 = snd (snd (snd r1))
        y2 = fst r2
        d2 = snd (snd (snd r2))
    in mkR Q tagAxContrapos (nd y1 y2)
           (thmTDispMp P Q y1 y2 y1' shape1 d1 d2)
  encodeRich (ruleInst x t {P = P} pf) =
    let rec = encodeRich pf
        y_h = fst rec
        y_h' = fst (snd rec)
        shape_h = fst (snd (snd rec))
        d_h = snd (snd (snd rec))
    in mkR (substF x t P) tagMp
           (nd (nd (code (var x)) (code t)) y_h)
           (thmTDispRuleInst x t P y_h y_h' shape_h d_h)
  encodeRich (ruleIndBT P v1 v2 pf_base pf_step) =
    let r1 = encodeRich pf_base
        r2 = encodeRich pf_step
        y_b = fst r1
        y_s = fst r2
        d_b = snd (snd (snd r1))
        d_s = snd (snd (snd r2))
    in mkR P tagRuleInst
           (nd (codeFormula P) (nd (code (var v1)) (nd (code (var v2)) (nd y_b y_s))))
           (thmTDispRuleIndBT P v1 v2 y_b y_s d_b d_s)
  encodeRich (ruleIndBT2 P v1 v2 v3 v4 pf_LL pf_LN pf_NL pf_PP) =
    let
        r_LL = encodeRich pf_LL
        r_LN = encodeRich pf_LN
        r_NL = encodeRich pf_NL
        r_PP = encodeRich pf_PP
        y_LL = fst r_LL
        y_LN = fst r_LN
        y_NL = fst r_NL
        y_PP = fst r_PP
        y_step = nd y_LN (nd y_NL y_PP)
    in mkR P tagRuleInst
           (nd (codeFormula P)
               (nd (code (var zero))
                   (nd (code (var zero))
                       (nd y_LL y_step))))
           (thmTDispRuleIndBT_param P zero zero (reify y_LL) (reify y_step))

  -- Group I (10 axiom cases, all concrete dispatches).
  encodeRich (axI t) =
    mkR (atomic (eqn (ap1 I t) t)) zero (code t) (thmTDispAxI t)
  encodeRich (axFst a' b') =
    mkR (atomic (eqn (ap1 Fst (ap2 Pair a' b')) a')) tagAxI
        (nd (code a') (code b')) (thmTDispAxFst a' b')
  encodeRich (axSnd a' b') =
    mkR (atomic (eqn (ap1 Snd (ap2 Pair a' b')) b')) tagAxFst
        (nd (code a') (code b')) (thmTDispAxSnd a' b')
  encodeRich (axConst a' b') =
    mkR (atomic (eqn (ap2 Const a' b') a')) tagAxSnd
        (nd (code a') (code b')) (thmTDispAxConst a' b')
  encodeRich (axComp f g t) =
    mkR (atomic (eqn (ap1 (Comp f g) t) (ap1 f (ap1 g t)))) tagAxConst
        (nd (codeF1 f) (nd (codeF1 g) (code t))) (thmTDispAxComp f g t)
  encodeRich (axComp2 h' f g t) =
    mkR (atomic (eqn (ap1 (Comp2 h' f g) t) (ap2 h' (ap1 f t) (ap1 g t))))
        tagAxComp
        (nd (codeF2 h') (nd (codeF1 f) (nd (codeF1 g) (code t))))
        (thmTDispAxComp2 h' f g t)
  encodeRich (axLift f a' b') =
    mkR (atomic (eqn (ap2 (Lift f) a' b') (ap1 f a'))) tagAxComp2
        (nd (codeF1 f) (nd (code a') (code b'))) (thmTDispAxLift f a' b')
  encodeRich (axPost f h' a' b') =
    mkR (atomic (eqn (ap2 (Post f h') a' b') (ap1 f (ap2 h' a' b'))))
        tagAxLift
        (nd (codeF1 f) (nd (codeF2 h') (nd (code a') (code b'))))
        (thmTDispAxPost f h' a' b')
  encodeRich (axFan h1 h2 h' a' b') =
    mkR (atomic (eqn (ap2 (Fan h1 h2 h') a' b')
                      (ap2 h' (ap2 h1 a' b') (ap2 h2 a' b'))))
        tagAxPost
        (nd (codeF2 h1) (nd (codeF2 h2) (nd (codeF2 h') (nd (code a') (code b')))))
        (thmTDispAxFan h1 h2 h' a' b')
  encodeRich (axZ x) =
    mkR (atomic (eqn (ap1 Z x) O)) tagAxFan
        (nd (codeF1 Z) (code x)) (thmTDispAxZ x)

  -- Group II (deferred non-recursive: axRecLf and axRecNd removed,
  -- so the surviving cases start at axIfLfL).  Predecessor of
  -- axIfLfL is now tagAxKT directly.
  encodeRich (axIfLfL a' b') =
    mkR (atomic (eqn (ap2 IfLf O (ap2 Pair a' b')) a')) tagAxKT
        (nd (code a') (code b')) (thmTDispAxIfLfL a' b')
  encodeRich (axIfLfN x y a' b') =
    mkR (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair a' b')) b'))
        tagAxIfLfL
        (nd (code x) (nd (code y) (nd (code a') (code b'))))
        (thmTDispAxIfLfN x y a' b')
  encodeRich axTreeEqLL =
    mkR (atomic (eqn (ap2 TreeEq O O) O)) tagAxIfLfN lf thmTDispAxTreeEqLL
  encodeRich (axTreeEqLN a' b') =
    mkR (atomic (eqn (ap2 TreeEq O (ap2 Pair a' b')) (ap2 Pair O O)))
        tagAxTreeEqLL
        (nd (code a') (code b')) (thmTDispAxTreeEqLN a' b')
  encodeRich (axTreeEqNL a' b') =
    mkR (atomic (eqn (ap2 TreeEq (ap2 Pair a' b') O) (ap2 Pair O O)))
        tagAxTreeEqLN
        (nd (code a') (code b')) (thmTDispAxTreeEqNL a' b')
  encodeRich (axTreeEqNN a1 a2 b1 b2) =
    mkR (atomic (eqn (ap2 TreeEq (ap2 Pair a1 a2) (ap2 Pair b1 b2))
                      (ap2 IfLf (ap2 TreeEq a1 b1)
                                (ap2 Pair (ap2 TreeEq a2 b2)
                                          (ap2 Pair O O)))))
        tagAxTreeEqNL
        (nd (code a1) (nd (code a2) (nd (code b1) (code b2))))
        (thmTDispAxTreeEqNN a1 a2 b1 b2)
  encodeRich (axGoodstein a' b') =
    mkR (atomic (eqn (ap2 IfLf (ap2 TreeEq a' b') (ap2 Pair a' O))
                      (ap2 IfLf (ap2 TreeEq a' b') (ap2 Pair b' O))))
        tagAxTreeEqNN
        (nd (code a') (code b')) (thmTDispAxGoodstein a' b')

  -- Group III (axRefl + 5 recursive).  axRefl, ruleSym are concrete;
  -- ruleTrans is concrete (uses head-shape from r1); cong1, congL,
  -- congR remain deferred.
  encodeRich (axRefl t) =
    mkR (atomic (eqn t t)) tagAxGoodstein (code t) (thmTDispAxRefl t)
  encodeRich (ruleSym {t = t} {u = u} pf) =
    let rec = encodeRich pf
        y_h = fst rec
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn u t)) tagAxRefl y_h
           (thmTDispRuleSym t u y_h d_h)
  encodeRich (ruleTrans {t = t} {u = u} {v = v} pf1 pf2) =
    let r1 = encodeRich pf1
        r2 = encodeRich pf2
        y1 = fst r1
        y1' = fst (snd r1)
        shape1 = fst (snd (snd r1))
        d1 = snd (snd (snd r1))
        y2 = fst r2
        d2 = snd (snd (snd r2))
    in mkR (atomic (eqn t v)) tagRuleSym (nd y1 y2)
           (thmTDispRuleTrans t u v y1 y2 y1' shape1 d1 d2)
  encodeRich (cong1 f {t = t} {u = u} pf) =
    let rec = encodeRich pf
        y_h = fst rec
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn (ap1 f t) (ap1 f u))) tagRuleTrans
           (nd (codeF1 f) y_h)
           (thmTDispCong1 f t u y_h d_h)
  encodeRich (congL g {t = t} {u = u} x pf) =
    let rec = encodeRich pf
        y_h = fst rec
        y_h' = fst (snd rec)
        shape_h = fst (snd (snd rec))
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn (ap2 g t x) (ap2 g u x))) tagCong1
           (nd (nd (codeF2 g) (code x)) y_h)
           (thmTDispCongL g x t u y_h y_h' shape_h d_h)
  encodeRich (congR g x {t = t} {u = u} pf) =
    let rec = encodeRich pf
        y_h = fst rec
        y_h' = fst (snd rec)
        shape_h = fst (snd (snd rec))
        d_h = snd (snd (snd rec))
    in mkR (atomic (eqn (ap2 g x t) (ap2 g x u))) tagCongL
           (nd (nd (codeF2 g) (code x)) y_h)
           (thmTDispCongR g x t u y_h y_h' shape_h d_h)

  -- Group IV (deferred non-recursive: axEqTrans..axContrapos).
  encodeRich (axEqTrans a' b' c') =
    mkR ((atomic (eqn a' b'))
          imp ((atomic (eqn a' c'))
                imp (atomic (eqn b' c'))))
        tagCongR
        (nd (code a') (nd (code b') (code c')))
        (thmTDispAxEqTrans a' b' c')
  encodeRich (axEqCong1 f a' b') =
    mkR ((atomic (eqn a' b'))
          imp (atomic (eqn (ap1 f a') (ap1 f b'))))
        tagAxEqTrans
        (nd (codeF1 f) (nd (code a') (code b')))
        (thmTDispAxEqCong1 f a' b')
  encodeRich (axEqCongL g a' b' c') =
    mkR ((atomic (eqn a' b'))
          imp (atomic (eqn (ap2 g a' c') (ap2 g b' c'))))
        tagAxEqCong1
        (nd (codeF2 g) (nd (code a') (nd (code b') (code c'))))
        (thmTDispAxEqCongL g a' b' c')
  encodeRich (axEqCongR g a' b' c') =
    mkR ((atomic (eqn a' b'))
          imp (atomic (eqn (ap2 g c' a') (ap2 g c' b'))))
        tagAxEqCongL
        (nd (codeF2 g) (nd (code a') (nd (code b') (code c'))))
        (thmTDispAxEqCongR g a' b' c')
  encodeRich (axK P Q) =
    mkR (P imp (Q imp P)) tagAxEqCongR
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxK P Q)
  encodeRich (axS P Q R) =
    mkR ((P imp (Q imp R)) imp ((P imp Q) imp (P imp R))) tagAxK
        (nd (codeFormula P) (nd (codeFormula Q) (codeFormula R)))
        (thmTDispAxS P Q R)
  encodeRich (axNeg P Q) =
    mkR ((not P) imp ((not Q) imp (Q imp P))) tagAxS
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxNeg P Q)
  encodeRich (axExFalso P Q) =
    mkR (P imp ((not P) imp Q)) tagAxNeg
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxExFalso P Q)
  encodeRich (axContrapos P Q) =
    mkR ((P imp Q) imp ((not Q) imp (not P))) tagAxExFalso
        (nd (codeFormula P) (codeFormula Q)) (thmTDispAxContrapos P Q)

  -- Group V (4 safe-default axioms).
  encodeRich axFstLf =
    mkR (atomic (eqn (ap1 Fst O) O)) tagRuleIndBT lf thmTDispAxFstLf
  encodeRich axSndLf =
    mkR (atomic (eqn (ap1 Snd O) O)) tagAxFstLf lf thmTDispAxSndLf
  encodeRich axIfLfLL =
    mkR (atomic (eqn (ap2 IfLf O O) O)) tagAxSndLf lf thmTDispAxIfLfLL
  encodeRich (axIfLfNL x y) =
    mkR (atomic (eqn (ap2 IfLf (ap2 Pair x y) O) O)) tagAxIfLfLL
        (nd (code x) (code y)) (thmTDispAxIfLfNL x y)
  encodeRich (axTreeRecLf f s p) =
    mkR (atomic (eqn (ap2 (treeRec f s) p O) (ap1 f p))) tagRuleIndBT2
        (nd (codeF1 f) (nd (codeF2 s) (code p)))
        (thmTDispAxTreeRecLf f s p)
  encodeRich (axTreeRecNd f s p a' b') =
    mkR (atomic (eqn (ap2 (treeRec f s) p (ap2 Pair a' b'))
                      (ap2 s (ap2 Pair p (ap2 Pair a' b'))
                             (ap2 Pair (ap2 (treeRec f s) p a')
                                       (ap2 (treeRec f s) p b')))))
        tagAxTreeRecLf
        (nd (codeF1 f) (nd (codeF2 s) (nd (code p) (nd (code a') (code b')))))
        (thmTDispAxTreeRecNd f s p a' b')
  -- Lite projection for  BRA.Thm11.Thm11 .
  encode : (P : Formula) -> Deriv P ->
           Sigma Tree (\ y ->
             Deriv (atomic (eqn (ap1 thmT (reify y))
                                 (reify (codeFormula P)))))
  encode P pf =
    let r = encodeRich pf
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
