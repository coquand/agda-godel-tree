{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.EvalHelpers
--
-- Equational reasoning helpers used by the body-evaluation lemmas of
-- the cascade dispatchers in BRA2.Thm.ThmT (and per-axiom Parts/Ax*.agda
-- files).
--
-- Two layers:
--
--   (1) Public lifted-deduction combinators.  Used to thread
--        Deriv (P imp ...)  hypotheses through equational reasoning
--       without extra `mp ... (axK ...) ...` boilerplate at every step.
--       Built from axK / axS / axEqTrans / axEqCong* / mp.
--
--   (2) Position-extractors and pair-builders for the standard payT
--       layout  Pair tag (Pair x1 (Pair x2 ...))  used by the encX /
--       outX coding.  These let body_axX_eval write
--        ext_x1 = liftCompFstSnd_evalPair tagCode_X x1 rest bb
--       instead of unfolding axComp / axLift / axSnd by hand.
--
-- Layer (2) is `abstract` to keep heavy normalisation localised; layer (1)
-- is public.  No postulates, no holes, no dot patterns.

module BRA2.Thm.EvalHelpers where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold

------------------------------------------------------------------------
-- (1) Lift helpers (deduction-theorem combinators).

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
-- Level-2 lift helpers: same as level-1 but operating two layers deep.
-- Used by doubly-lifted dispatchers for basePair_param construction
-- (Theorem 12 Rec/RecP universal closure under TWO IH hypotheses).

liftAxiomTwo : (P1 P2 : Formula) {Q : Formula} ->
               Deriv Q -> Deriv (P1 imp (P2 imp Q))
liftAxiomTwo P1 P2 D = liftAxiom P1 (liftAxiom P2 D)

B_combinatorTwo : {P1 P2 Q R : Formula} ->
                  Deriv (P1 imp (P2 imp (Q imp R))) ->
                  Deriv (P1 imp (P2 imp Q)) ->
                  Deriv (P1 imp (P2 imp R))
B_combinatorTwo {P1} {P2} {Q} {R} D1 D2 =
  B_combinator (B_combinator (liftAxiom P1 (axS P2 Q R)) D1) D2

liftedAxEqTransTwo : (P1 P2 : Formula) (a b c : Term) ->
                     Deriv (P1 imp (P2 imp atomic (eqn a b))) ->
                     Deriv (P1 imp (P2 imp atomic (eqn a c))) ->
                     Deriv (P1 imp (P2 imp atomic (eqn b c)))
liftedAxEqTransTwo P1 P2 a b c D1 D2 =
  B_combinatorTwo (B_combinatorTwo (liftAxiomTwo P1 P2 (axEqTrans a b c)) D1) D2

liftedRuleSymTwo : (P1 P2 : Formula) (a b : Term) ->
                   Deriv (P1 imp (P2 imp atomic (eqn a b))) ->
                   Deriv (P1 imp (P2 imp atomic (eqn b a)))
liftedRuleSymTwo P1 P2 a b D =
  liftedAxEqTransTwo P1 P2 a b a D (liftAxiomTwo P1 P2 (axRefl a))

liftedRuleTransTwo : (P1 P2 : Formula) (a b c : Term) ->
                     Deriv (P1 imp (P2 imp atomic (eqn a b))) ->
                     Deriv (P1 imp (P2 imp atomic (eqn b c))) ->
                     Deriv (P1 imp (P2 imp atomic (eqn a c)))
liftedRuleTransTwo P1 P2 a b c D1 D2 =
  liftedAxEqTransTwo P1 P2 b a c (liftedRuleSymTwo P1 P2 a b D1) D2

liftedCong1Two : (P1 P2 : Formula) (f : Fun1) (a b : Term) ->
                 Deriv (P1 imp (P2 imp atomic (eqn a b))) ->
                 Deriv (P1 imp (P2 imp atomic (eqn (ap1 f a) (ap1 f b))))
liftedCong1Two P1 P2 f a b D =
  B_combinatorTwo (liftAxiomTwo P1 P2 (axEqCong1 f a b)) D

liftedCongLTwo : (P1 P2 : Formula) (g : Fun2) (a b c : Term) ->
                 Deriv (P1 imp (P2 imp atomic (eqn a b))) ->
                 Deriv (P1 imp (P2 imp atomic (eqn (ap2 g a c) (ap2 g b c))))
liftedCongLTwo P1 P2 g a b c D =
  B_combinatorTwo (liftAxiomTwo P1 P2 (axEqCongL g a b c)) D

liftedCongRTwo : (P1 P2 : Formula) (g : Fun2) (a b c : Term) ->
                 Deriv (P1 imp (P2 imp atomic (eqn a b))) ->
                 Deriv (P1 imp (P2 imp atomic (eqn (ap2 g c a) (ap2 g c b))))
liftedCongRTwo P1 P2 g a b c D =
  B_combinatorTwo (liftAxiomTwo P1 P2 (axEqCongR g a b c)) D

------------------------------------------------------------------------
-- (2) Position-extractors and pair-builders.
--
-- The standard input layout is  a = Pair tag payT  where
--  payT = Pair x1 (Pair x2 ... (Pair xN-1 xN)) .  These helpers extract
-- a single position xK or build a result of the form  Pair X Y .

abstract

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

  -- ap2 (Lift (KT v)) a b = v .  (IsValue-indexed.)
  liftKT_eval : (v : Term) -> IsValue v -> (a b : Term) ->
    Deriv (atomic (eqn (ap2 (Lift (KT v)) a b) v))
  liftKT_eval v iv a b = ruleTrans (axLift (KT v) a b) (axKT v iv a)

  -- ap2 (Fan (Lift (KT Kv)) X Pair) a b = Pair Kv xRes  given X a b = xRes.
  pairOfConst_eval : (Kv : Term) -> IsValue Kv -> (X : Fun2) (a b xRes : Term) ->
    Deriv (atomic (eqn (ap2 X a b) xRes)) ->
    Deriv (atomic (eqn (ap2 (Fan (Lift (KT Kv)) X Pair) a b)
                       (ap2 Pair Kv xRes)))
  pairOfConst_eval Kv iKv X a b xRes Xeq =
    let K : Term
        K = Kv
        f1 : Deriv (atomic (eqn (ap2 (Fan (Lift (KT K)) X Pair) a b)
                                 (ap2 Pair (ap2 (Lift (KT K)) a b) (ap2 X a b))))
        f1 = axFan (Lift (KT K)) X Pair a b
        kt1 : Deriv (atomic (eqn (ap2 (Lift (KT K)) a b) K))
        kt1 = liftKT_eval Kv iKv a b
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

  pairOfConst_eval_lifted : (P : Formula) (Kv : Term) -> IsValue Kv ->
                            (X : Fun2) (a b xRes : Term) ->
    Deriv (P imp atomic (eqn (ap2 X a b) xRes)) ->
    Deriv (P imp atomic (eqn (ap2 (Fan (Lift (KT Kv)) X Pair) a b)
                              (ap2 Pair Kv xRes)))
  pairOfConst_eval_lifted P Kv iKv X a b xRes Xeq =
    let K : Term
        K = Kv
        f1 = axFan (Lift (KT K)) X Pair a b
        kt1 = liftKT_eval Kv iKv a b
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

  -- Doubly-lifted variants for basePair_param construction.

  pairOfConst_eval_doublelifted : (P1 P2 : Formula) (Kv : Term) -> IsValue Kv ->
                                  (X : Fun2) (a b xRes : Term) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap2 X a b) xRes))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap2 (Fan (Lift (KT Kv)) X Pair) a b)
                                       (ap2 Pair Kv xRes))))
  pairOfConst_eval_doublelifted P1 P2 Kv iKv X a b xRes Xeq =
    let K : Term
        K = Kv
        f1 = axFan (Lift (KT K)) X Pair a b
        kt1 = liftKT_eval Kv iKv a b
        e1 = congL Pair (ap2 X a b) kt1
        lifted_combined : Deriv (P1 imp (P2 imp atomic
          (eqn (ap2 (Fan (Lift (KT K)) X Pair) a b) (ap2 Pair K (ap2 X a b)))))
        lifted_combined = liftAxiomTwo P1 P2 (ruleTrans f1 e1)
        lifted_e2 : Deriv (P1 imp (P2 imp atomic
          (eqn (ap2 Pair K (ap2 X a b)) (ap2 Pair K xRes))))
        lifted_e2 = liftedCongRTwo P1 P2 Pair (ap2 X a b) xRes K Xeq
    in liftedRuleTransTwo P1 P2
         (ap2 (Fan (Lift (KT K)) X Pair) a b)
         (ap2 Pair K (ap2 X a b))
         (ap2 Pair K xRes)
         lifted_combined lifted_e2

  pairOfFan_eval_doublelifted : (P1 P2 : Formula) (X Y : Fun2) (a b xRes yRes : Term) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap2 X a b) xRes))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap2 Y a b) yRes))) ->
    Deriv (P1 imp (P2 imp atomic (eqn (ap2 (Fan X Y Pair) a b) (ap2 Pair xRes yRes))))
  pairOfFan_eval_doublelifted P1 P2 X Y a b xRes yRes Xeq Yeq =
    let f1 = axFan X Y Pair a b
        lifted_f1 : Deriv (P1 imp (P2 imp atomic
          (eqn (ap2 (Fan X Y Pair) a b) (ap2 Pair (ap2 X a b)(ap2 Y a b)))))
        lifted_f1 = liftAxiomTwo P1 P2 f1
        lifted_e1 : Deriv (P1 imp (P2 imp atomic
          (eqn (ap2 Pair (ap2 X a b)(ap2 Y a b)) (ap2 Pair xRes (ap2 Y a b)))))
        lifted_e1 = liftedCongLTwo P1 P2 Pair (ap2 X a b) xRes (ap2 Y a b) Xeq
        lifted_e2 : Deriv (P1 imp (P2 imp atomic
          (eqn (ap2 Pair xRes (ap2 Y a b)) (ap2 Pair xRes yRes))))
        lifted_e2 = liftedCongRTwo P1 P2 Pair (ap2 Y a b) yRes xRes Yeq
    in liftedRuleTransTwo P1 P2
         (ap2 (Fan X Y Pair) a b)
         (ap2 Pair (ap2 X a b)(ap2 Y a b))
         (ap2 Pair xRes yRes)
         lifted_f1
         (liftedRuleTransTwo P1 P2
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

  -- Depth 3, "left-Pair" payload: a = Pair tag (Pair (Pair p1 p2) p3).
  -- Used by  body_congL / body_congR  in the new (Finding 1) layout
  -- where the open IH-input  y_h_T = p3  sits at the outer Snd, and the
  -- closed pair  (codeF2 g, xT) = Pair p1 p2  sits at the inner Fst.

  -- ap2 (Lift (Comp Fst (Comp Fst Snd))) (Pair tag (Pair (Pair p1 p2) p3)) b = p1.
  liftFstFstSnd_evalPairLP : (tag p1 p2 p3 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Fst (Comp Fst Snd)))
            (ap2 Pair tag (ap2 Pair (ap2 Pair p1 p2) p3)) b)
      p1))
  liftFstFstSnd_evalPairLP tag p1 p2 p3 b =
    let a = ap2 Pair tag (ap2 Pair (ap2 Pair p1 p2) p3)
        fstSnd : Deriv (atomic (eqn (ap1 (Comp Fst Snd) a) (ap2 Pair p1 p2)))
        fstSnd =
          let c1 = axComp Fst Snd a
              c2 = axSnd tag (ap2 Pair (ap2 Pair p1 p2) p3)
              c3 = cong1 Fst c2
              c4 = axFst (ap2 Pair p1 p2) p3
          in ruleTrans c1 (ruleTrans c3 c4)
    in liftComp_eval Fst (Comp Fst Snd) a b (ap2 Pair p1 p2) p1 fstSnd
         (axFst p1 p2)

  -- ap2 (Lift (Comp Snd (Comp Fst Snd))) (Pair tag (Pair (Pair p1 p2) p3)) b = p2.
  liftSndFstSnd_evalPairLP : (tag p1 p2 p3 b : Term) ->
    Deriv (atomic (eqn
      (ap2 (Lift (Comp Snd (Comp Fst Snd)))
            (ap2 Pair tag (ap2 Pair (ap2 Pair p1 p2) p3)) b)
      p2))
  liftSndFstSnd_evalPairLP tag p1 p2 p3 b =
    let a = ap2 Pair tag (ap2 Pair (ap2 Pair p1 p2) p3)
        fstSnd : Deriv (atomic (eqn (ap1 (Comp Fst Snd) a) (ap2 Pair p1 p2)))
        fstSnd =
          let c1 = axComp Fst Snd a
              c2 = axSnd tag (ap2 Pair (ap2 Pair p1 p2) p3)
              c3 = cong1 Fst c2
              c4 = axFst (ap2 Pair p1 p2) p3
          in ruleTrans c1 (ruleTrans c3 c4)
    in liftComp_eval Snd (Comp Fst Snd) a b (ap2 Pair p1 p2) p2 fstSnd
         (axSnd p1 p2)

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
        c2 = axComp Snd Snd a
        c3 = cong1 Snd c2
        c4 = sndOf_d3 tag x1 x2 (ap2 Pair x3 x4)
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
