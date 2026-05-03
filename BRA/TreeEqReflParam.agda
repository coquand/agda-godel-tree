{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.TreeEqReflParam
--
-- Parametric reflexivity:
--   treeEqReflParam : (t : Term) ->
--     Deriv (atomic (eqn (ap2 TreeEq t t) O))
--
-- Generalises BRA.SubT.treeEqRed (which works only for closed Tree
-- inputs of the form  reify a , reify b ) to an arbitrary Term t.
-- Used by  body_mp_v_eval_pass  (BRA.SoundMpVProof) when its inner
-- check  TreeEq pT pT  needs to be discharged for an open  pT
-- carried under  PrAtX x  in Theorem 14's mp dispatcher.
--
-- Construction.  By  ruleIndBT  on motive
--    M : atomic (eqn (ap2 TreeEq (var 0) (var 0)) O)
-- with fresh variables  v1 := suc zero ,  v2 := suc (suc zero) :
--   * Base (var 0 := O) : axTreeEqLL.
--   * Step (var 0 := Pair v1 v2 with IH1, IH2):
--       axTreeEqNN reduces TreeEq (Pair v1 v2)(Pair v1 v2) to
--       IfLf (TreeEq v1 v1)(Pair (TreeEq v2 v2)(Pair O O)) ;
--       IH1 rewrites TreeEq v1 v1 -> O ; axIfLfL reduces
--       IfLf O (Pair X (Pair O O)) to X = TreeEq v2 v2 ;
--       IH2 rewrites that to O.
-- Then  ruleInst zero t  specializes the conclusion to arbitrary  t .
--
-- The step-implication is built via liftAxiomTwo / liftedRuleTransTwo
-- / liftedCongLTwo from BRA.Thm.EvalHelpers (Hilbert/Carneiro-style
-- two-hypothesis lifts), plus a single  Q imp Q  identity proof for
-- accessing IH2 in the doubly-lifted context.
--
-- ASCII only.  No postulates, no holes, no with-abstraction.

module BRA.TreeEqReflParam where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.EvalHelpers
  using (liftAxiom ; liftAxiomTwo ; liftedRuleTransTwo ; liftedCongLTwo)

------------------------------------------------------------------------
-- Identity implication  Q imp Q  via S, K, K.
--
--   axS Q (Q imp Q) Q : (Q imp ((Q imp Q) imp Q)) imp ((Q imp (Q imp Q)) imp (Q imp Q))
--   axK Q (Q imp Q)   :  Q imp ((Q imp Q) imp Q)
--   mp the two:        : (Q imp (Q imp Q)) imp (Q imp Q)
--   axK Q Q           :  Q imp (Q imp Q)
--   mp the two:        :  Q imp Q

idImp : (Q : Formula) -> Deriv (Q imp Q)
idImp Q = mp (mp (axS Q (Q imp Q) Q) (axK Q (Q imp Q))) (axK Q Q)

------------------------------------------------------------------------
-- The motive and its three substituted instances.

motiveTreeEqRefl : Formula
motiveTreeEqRefl = atomic (eqn (ap2 TreeEq (var zero) (var zero)) O)

------------------------------------------------------------------------
-- The base-O case typechecks because
--   substF zero O motiveTreeEqRefl
--    = atomic (eqn (ap2 TreeEq O O) O)
-- by definitional reduction of  natEq zero zero = true ,
-- boolCase true _ _ = first arg.

baseTreeEqReflO : Deriv (substF zero O motiveTreeEqRefl)
baseTreeEqReflO = axTreeEqLL

------------------------------------------------------------------------
-- The step case: assuming IH1 = (TreeEq v1 v1 = O) and
-- IH2 = (TreeEq v2 v2 = O), prove (TreeEq (Pair v1 v2)(Pair v1 v2) = O).

stepTreeEqRefl :
  Deriv ((substF zero (var (suc zero))             motiveTreeEqRefl) imp
         ((substF zero (var (suc (suc zero)))       motiveTreeEqRefl) imp
          (substF zero (ap2 Pair (var (suc zero))
                                 (var (suc (suc zero)))) motiveTreeEqRefl)))
stepTreeEqRefl =
  let
    v1T : Term
    v1T = var (suc zero)
    v2T : Term
    v2T = var (suc (suc zero))
    eqV1V1 : Term
    eqV1V1 = ap2 TreeEq v1T v1T
    eqV2V2 : Term
    eqV2V2 = ap2 TreeEq v2T v2T
    pairV1V2 : Term
    pairV1V2 = ap2 Pair v1T v2T

    IH1 : Formula
    IH1 = atomic (eqn eqV1V1 O)
    IH2 : Formula
    IH2 = atomic (eqn eqV2V2 O)

    -- Reach IH1 inside the doubly-lifted context.
    --   axK IH1 IH2 : Deriv (IH1 imp (IH2 imp IH1))
    accessIH1 : Deriv (IH1 imp (IH2 imp IH1))
    accessIH1 = axK IH1 IH2

    -- Reach IH2 inside the doubly-lifted context.
    --   idImp IH2 : Deriv (IH2 imp IH2)
    --   liftAxiom IH1 (idImp IH2) : Deriv (IH1 imp (IH2 imp IH2))
    accessIH2 : Deriv (IH1 imp (IH2 imp IH2))
    accessIH2 = liftAxiom IH1 (idImp IH2)

    -- 1. axTreeEqNN reduction  (closed at v1T, v2T).
    nnRhs : Term
    nnRhs = ap2 IfLf eqV1V1 (ap2 Pair eqV2V2 (ap2 Pair O O))
    nnAt : Deriv (atomic (eqn (ap2 TreeEq pairV1V2 pairV1V2) nnRhs))
    nnAt = axTreeEqNN v1T v2T v1T v2T

    nnL : Deriv (IH1 imp (IH2 imp atomic (eqn (ap2 TreeEq pairV1V2 pairV1V2) nnRhs)))
    nnL = liftAxiomTwo IH1 IH2 nnAt

    -- 2. Substitute IH1 in the IfLf left position via liftedCongLTwo.
    nnRhsAfterIH1 : Term
    nnRhsAfterIH1 = ap2 IfLf O (ap2 Pair eqV2V2 (ap2 Pair O O))

    cstepL : Deriv (IH1 imp (IH2 imp atomic (eqn nnRhs nnRhsAfterIH1)))
    cstepL = liftedCongLTwo IH1 IH2 IfLf eqV1V1 O
               (ap2 Pair eqV2V2 (ap2 Pair O O)) accessIH1

    -- 3. axIfLfL: IfLf O (Pair eqV2V2 (Pair O O)) = eqV2V2 .
    iflfLAt : Deriv (atomic (eqn nnRhsAfterIH1 eqV2V2))
    iflfLAt = axIfLfL eqV2V2 (ap2 Pair O O)

    iflfLLL : Deriv (IH1 imp (IH2 imp atomic (eqn nnRhsAfterIH1 eqV2V2)))
    iflfLLL = liftAxiomTwo IH1 IH2 iflfLAt

    -- 4. Chain.
    chain12 : Deriv (IH1 imp (IH2 imp atomic
                (eqn (ap2 TreeEq pairV1V2 pairV1V2) nnRhsAfterIH1)))
    chain12 = liftedRuleTransTwo IH1 IH2
                (ap2 TreeEq pairV1V2 pairV1V2) nnRhs nnRhsAfterIH1
                nnL cstepL

    chain123 : Deriv (IH1 imp (IH2 imp atomic
                 (eqn (ap2 TreeEq pairV1V2 pairV1V2) eqV2V2)))
    chain123 = liftedRuleTransTwo IH1 IH2
                 (ap2 TreeEq pairV1V2 pairV1V2) nnRhsAfterIH1 eqV2V2
                 chain12 iflfLLL

    chain1234 : Deriv (IH1 imp (IH2 imp atomic
                  (eqn (ap2 TreeEq pairV1V2 pairV1V2) O)))
    chain1234 = liftedRuleTransTwo IH1 IH2
                  (ap2 TreeEq pairV1V2 pairV1V2) eqV2V2 O
                  chain123 accessIH2
  in chain1234

------------------------------------------------------------------------
-- The closed-formula reflexivity (var 0 free).

treeEqReflClosed : Deriv motiveTreeEqRefl
treeEqReflClosed =
  ruleIndBT motiveTreeEqRefl (suc zero) (suc (suc zero))
            baseTreeEqReflO stepTreeEqRefl

------------------------------------------------------------------------
-- The parametric reflexivity:
--   substitute  t  for  var 0  via  ruleInst .
-- Result type:  substF zero t motiveTreeEqRefl
--             = atomic (eqn (ap2 TreeEq t t) O)
-- by definitional reduction of  subst zero t (var zero) = t .

treeEqReflParam : (t : Term) ->
  Deriv (atomic (eqn (ap2 TreeEq t t) O))
treeEqReflParam t = ruleInst zero t treeEqReflClosed
