{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.TagCodes
--
-- Reified tag-code constants used by the cascade dispatchers and the
-- per-axiom body / body_eval lemmas.
--
-- Two families:
--
--   tagCode_axX, tagCode_ruleX  --  reify (natCode tagX) , the input-tag
--     of the proof-code for primitive X.  Used in encX, in body_axX_eval
--     LHS, and in skipAtTag / hitAtTag entries.
--
--   tagCode_XFunc                --  reify (leftT (codeF? (X _ ...))) ,
--     the leading natCode tag in the codeF1/codeF2 tree of functor X.
--     Used inside body_axX expressions to construct LHS-code Fragments
--     of the form  Pair tagCode_XFunc  (Pair payF payS) .
--
-- Defined OUTSIDE any abstract block so that downstream signatures may
-- name the constants without forcing unfolding.

module BRA2.Thm.TagCodes where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Thm.Tag

------------------------------------------------------------------------
-- Reified tag codes (44).

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
-- tagCode_axRecLf and tagCode_axRecNd removed (axRecLf / axRecNd
-- demoted to derived lemmas).
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
-- tagCode_recFunc removed (Rec demoted to defined function over treeRec).
tagCode_ifLfFunc    : Term
tagCode_ifLfFunc    = reify (leftT (codeF2 IfLf))
tagCode_treeEqFunc  : Term
tagCode_treeEqFunc  = reify (leftT (codeF2 TreeEq))

------------------------------------------------------------------------
-- Unified tree-recursor (axTreeRecLf, axTreeRecNd).

tagCode_axTreeRecLf : Term
tagCode_axTreeRecLf = reify (natCode tagAxTreeRecLf)

tagCode_axTreeRecNd : Term
tagCode_axTreeRecNd = reify (natCode tagAxTreeRecNd)

tagCode_treeRecFunc : Term
tagCode_treeRecFunc = reify (leftT (codeF2 (treeRec I IfLf)))
