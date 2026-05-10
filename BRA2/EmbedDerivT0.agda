{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.EmbedDerivT0 -- structural embedding from the open fragment
-- DerivT0  back into the bounded threshold system  DerivTBounded
-- at rank 0.
--
-- Each DerivT0 constructor maps to its same-named DerivTBounded
-- counterpart with rank 0 and the structurally-determined level.
-- Computation axioms / propositional axioms / atomic structural
-- rules / ruleInst land at level 0 ; mp adds 1 to its premises'
-- max-level.
--
-- The embedding signature
--
--   embedDerivT0 : DerivT0 P -> Sigma Nat (\ l -> DerivTBounded 0 l P)
--
-- is the natural inverse of the rankZero forgetful map (modulo
-- level reconstruction).  Useful for plugging an open-fragment
-- result back into the bounded framework -- e.g., supplying a
-- DerivTBounded 0 _ bot  to the rank-r generalisation of
-- BoundedReductionTheorem .

module BRA2.EmbedDerivT0 where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
import BRA2.DerivT0       as O
import BRA2.DerivTBounded as B
open import BRA2.DerivTBounded using (DerivTBounded ; natMax)

------------------------------------------------------------------------
-- The embedding.

embedDerivT0 :
  {P : Formula} -> O.DerivT0 P ->
  Sigma Nat (\ l -> DerivTBounded zero l P)

------------------------------------------------------------------------
-- Computation axioms : level 0.

embedDerivT0 (O.axI t)              = mkSigma zero (B.axIB zero zero t)
embedDerivT0 (O.axFst a b)          = mkSigma zero (B.axFstB zero zero a b)
embedDerivT0 (O.axSnd a b)          = mkSigma zero (B.axSndB zero zero a b)
embedDerivT0 O.axFstLf              = mkSigma zero (B.axFstLfB zero zero)
embedDerivT0 O.axSndLf              = mkSigma zero (B.axSndLfB zero zero)
embedDerivT0 (O.axConst a b)        = mkSigma zero (B.axConstB zero zero a b)
embedDerivT0 (O.axComp f g t)       = mkSigma zero (B.axCompB zero zero f g t)
embedDerivT0 (O.axComp2 h f g t)    = mkSigma zero (B.axComp2B zero zero h f g t)
embedDerivT0 (O.axLift f a b)       = mkSigma zero (B.axLiftB zero zero f a b)
embedDerivT0 (O.axPost f h a b)     = mkSigma zero (B.axPostB zero zero f h a b)
embedDerivT0 (O.axFan h1 h2 h a b)  = mkSigma zero (B.axFanB zero zero h1 h2 h a b)
embedDerivT0 (O.axZ x)              = mkSigma zero (B.axZB zero zero x)
embedDerivT0 (O.axTreeRecLf f s p)  = mkSigma zero (B.axTreeRecLfB zero zero f s p)
embedDerivT0 (O.axTreeRecNd f s p a b) =
  mkSigma zero (B.axTreeRecNdB zero zero f s p a b)
embedDerivT0 (O.axIfLfL a b)        = mkSigma zero (B.axIfLfLB zero zero a b)
embedDerivT0 (O.axIfLfN x y a b)    = mkSigma zero (B.axIfLfNB zero zero x y a b)
embedDerivT0 O.axIfLfLL             = mkSigma zero (B.axIfLfLLB zero zero)
embedDerivT0 (O.axIfLfNL x y)       = mkSigma zero (B.axIfLfNLB zero zero x y)
embedDerivT0 O.axTreeEqLL           = mkSigma zero (B.axTreeEqLLB zero zero)
embedDerivT0 (O.axTreeEqLN a b)     = mkSigma zero (B.axTreeEqLNB zero zero a b)
embedDerivT0 (O.axTreeEqNL a b)     = mkSigma zero (B.axTreeEqNLB zero zero a b)
embedDerivT0 (O.axTreeEqNN a1 a2 b1 b2) =
  mkSigma zero (B.axTreeEqNNB zero zero a1 a2 b1 b2)
embedDerivT0 (O.axGoodstein a b)    = mkSigma zero (B.axGoodsteinB zero zero a b)
embedDerivT0 (O.axRefl t)           = mkSigma zero (B.axReflB zero zero t)

------------------------------------------------------------------------
-- Atomic structural rules : same level as input.

embedDerivT0 (O.ruleSym d) =
  let p = embedDerivT0 d
  in mkSigma (fst p) (B.ruleSymB (snd p))
embedDerivT0 (O.ruleTrans d1 d2) =
  let p1 = embedDerivT0 d1
      p2 = embedDerivT0 d2
  in mkSigma (natMax (fst p1) (fst p2)) (B.ruleTransB (snd p1) (snd p2))
embedDerivT0 (O.cong1 f d) =
  let p = embedDerivT0 d
  in mkSigma (fst p) (B.cong1B f (snd p))
embedDerivT0 (O.congL g x d) =
  let p = embedDerivT0 d
  in mkSigma (fst p) (B.congLB g x (snd p))
embedDerivT0 (O.congR g x d) =
  let p = embedDerivT0 d
  in mkSigma (fst p) (B.congRB g x (snd p))

------------------------------------------------------------------------
-- Equational implication / propositional axioms : level 0.

embedDerivT0 (O.axEqTrans a b c)    = mkSigma zero (B.axEqTransB zero zero a b c)
embedDerivT0 (O.axEqCong1 f a b)    = mkSigma zero (B.axEqCong1B zero zero f a b)
embedDerivT0 (O.axEqCongL g a b c)  = mkSigma zero (B.axEqCongLB zero zero g a b c)
embedDerivT0 (O.axEqCongR g a b c)  = mkSigma zero (B.axEqCongRB zero zero g a b c)
embedDerivT0 (O.axK P Q)            = mkSigma zero (B.axKB zero zero P Q)
embedDerivT0 (O.axS P Q R)          = mkSigma zero (B.axSB zero zero P Q R)
embedDerivT0 (O.axNeg P Q)          = mkSigma zero (B.axNegB zero zero P Q)

------------------------------------------------------------------------
-- mp : adds 1 to the max-level of the premises ; ruleInst : preserves.

embedDerivT0 (O.mp d1 d2) =
  let p1 = embedDerivT0 d1
      p2 = embedDerivT0 d2
  in mkSigma (suc (natMax (fst p1) (fst p2))) (B.mpB (snd p1) (snd p2))
embedDerivT0 (O.ruleInst x t d) =
  let p = embedDerivT0 d
  in mkSigma (fst p) (B.ruleInstB x t (snd p))
