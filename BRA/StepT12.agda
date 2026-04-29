{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.StepT12
--
-- Numeral-only Theorem 12: a meta-recursive proof-code generator
--   stepT12 : (F : Fun1) (i : Tree) -> Sigma Tree (\d ->
--               Deriv (atomic (eqn (ap1 thmT (reify d))
--                                   (reify (codeFormula
--                                     (atomic (eqn (ap1 F (reify i))
--                                                   (reify (evalFun1 F i)))))))))
--
-- Following the user's reformulation: Theorem 12 is implemented at canonical
-- (closed Tree) inputs only, by meta-recursion on the functor's definition.
-- The "free variable" of Guard's text is read schematically: an Agda parameter
-- i : Tree, instantiated by ordinary function application at the Goedel
-- numbers we need.
--
-- This file is the SCAFFOLD: evalFun1 / evalFun2 meta-evaluators + stepT12
-- type signature + atomic cases (I, Z) fully implemented.  The remaining
-- cases (Fst, Snd, Comp, Comp2, Rec, plus Fun2 cases for stepT12_2) follow
-- the templates documented in the file.
--
-- No postulates, no holes.

module BRA.StepT12 where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Thm.ThmT using
  ( thmT
  ; thmTDispAxI ; thmTDispAxZ
  ; thmTDispAxFst ; thmTDispAxFstLf
  ; thmTDispAxSnd ; thmTDispAxSndLf
  ; thmTDispAxComp ; thmTDispAxComp2
  ; thmTDispAxConst
  ; thmTDispAxLift ; thmTDispAxPost ; thmTDispAxFan
  ; thmTDispAxIfLfL ; thmTDispAxIfLfN
  ; thmTDispAxIfLfLL ; thmTDispAxIfLfNL
  ; thmTDispAxTreeEqLL ; thmTDispAxTreeEqLN ; thmTDispAxTreeEqNL
  ; thmTDispAxRefl
  ; thmTDispRuleTrans ; thmTDispCong1 ; thmTDispCongL ; thmTDispCongR
  ; tagCode_axComp ; tagCode_axComp2
  ; tagCode_axLift ; tagCode_axPost ; tagCode_axFan
  ; tagCode_ruleTrans ; tagCode_cong1
  ; tagCode_congL ; tagCode_congR )
open BRA.Thm.ThmT.WithDispatch using (encode ; encodeRich)
open import BRA.Thm.Parts.AxI    using (encAxI    ; outAxI)
open import BRA.Thm.Parts.AxKT   using (encAxZ    ; outAxZ)
open import BRA.Thm.Parts.AxFst  using (encAxFst  ; outAxFst)
open import BRA.Thm.Parts.AxFstLf using (encAxFstLf ; outAxFstLf)
open import BRA.Thm.Parts.AxSnd  using (encAxSnd  ; outAxSnd)
open import BRA.Thm.Parts.AxSndLf using (encAxSndLf ; outAxSndLf)
open import BRA.Thm.Parts.AxComp  using (encAxComp ; outAxComp)
open import BRA.Thm.Parts.RuleTrans using (encRuleTrans ; outRuleTrans)
open import BRA.Thm.Parts.Cong1   using (encCong1  ; outCong1)
open import BRA.Thm.Parts.AxConst   using (encAxConst   ; outAxConst)
open import BRA.Thm.Parts.AxRefl    using (encAxRefl    ; outAxRefl)
open import BRA.Thm.Parts.AxIfLfL   using (encAxIfLfL   ; outAxIfLfL)
open import BRA.Thm.Parts.AxIfLfN   using (encAxIfLfN   ; outAxIfLfN)
open import BRA.Thm.Parts.AxIfLfLL  using (encAxIfLfLL  ; outAxIfLfLL)
open import BRA.Thm.Parts.AxIfLfNL  using (encAxIfLfNL  ; outAxIfLfNL)
open import BRA.Thm.Parts.AxTreeEqLL using (encAxTreeEqLL ; outAxTreeEqLL)
open import BRA.Thm.Parts.AxTreeEqLN using (encAxTreeEqLN ; outAxTreeEqLN)
open import BRA.Thm.Parts.AxTreeEqNL using (encAxTreeEqNL ; outAxTreeEqNL)
open import BRA.Thm.Parts.AxComp2  using (encAxComp2 ; outAxComp2)
open import BRA.Thm.Parts.AxLift   using (encAxLift  ; outAxLift)
open import BRA.Thm.Parts.AxPost   using (encAxPost  ; outAxPost)
open import BRA.Thm.Parts.AxFan    using (encAxFan   ; outAxFan)
open import BRA.Thm.Parts.CongL    using (encCongL   ; outCongL)
open import BRA.Thm.Parts.CongR    using (encCongR   ; outCongR)

------------------------------------------------------------------------
-- treeEqual : separate Tree-equality evaluator (NOT in the evalFun1/
-- evalFun2 mutual block).  Defined here so its diagonal recursion on
-- (a, b) tree-pair structure is visible to Agda's termination checker.
--
-- treeEqual a b  reduces to  lf  when  a  and  b  are structurally equal,
-- and to  nd lf lf  otherwise.  This is the meta-level mirror of axTreeEqNN's
-- "if-equal-then-recurse" branching: combineEq propagates the result of
-- comparing  a1 vs b1  with  a2 vs b2 .

combineEq : Tree -> Tree -> Tree
combineEq lf       y = y
combineEq (nd _ _) _ = nd lf lf

treeEqual : Tree -> Tree -> Tree
treeEqual lf       lf       = lf
treeEqual lf       (nd _ _) = nd lf lf
treeEqual (nd _ _) lf       = nd lf lf
treeEqual (nd a1 a2) (nd b1 b2) = combineEq (treeEqual a1 b1) (treeEqual a2 b2)

------------------------------------------------------------------------
-- evalFun1 / evalFun2 : meta-evaluators on Fun1 / Fun2.
--
-- Defined fully on canonical Tree inputs.  evalFun2 TreeEq is now
-- implemented via the separate treeEqual evaluator above (replacing the
-- earlier placeholder for the NN case).

evalFun1 : Fun1 -> Tree -> Tree
evalFun2 : Fun2 -> Tree -> Tree -> Tree

evalFun1 I             i  = i
evalFun1 Fst           lf       = lf
evalFun1 Fst           (nd a b) = a
evalFun1 Snd           lf       = lf
evalFun1 Snd           (nd a b) = b
evalFun1 Z             i  = lf
evalFun1 (Comp f g)    i  = evalFun1 f (evalFun1 g i)
evalFun1 (Comp2 h f g) i  = evalFun2 h (evalFun1 f i) (evalFun1 g i)
-- Rec z s : meta-evaluates closed canonical z to its Tree behind reify.
-- For full generality, z = O is the typical case (= lf).  At non-canonical
-- z, this stub is a placeholder; real correctness requires z be canonical.
evalFun1 (Rec z s)     lf       = lf
evalFun1 (Rec z s)     (nd a b) =
  evalFun2 s (nd a b)
    (nd (evalFun1 (Rec z s) a) (evalFun1 (Rec z s) b))

evalFun2 Pair          a b = nd a b
evalFun2 Const         a b = a
evalFun2 (Lift f)      a b = evalFun1 f a
evalFun2 (Post f h)    a b = evalFun1 f (evalFun2 h a b)
evalFun2 (Fan h1 h2 h) a b = evalFun2 h (evalFun2 h1 a b) (evalFun2 h2 a b)
evalFun2 IfLf          lf       (nd c d) = c
evalFun2 IfLf          (nd _ _) (nd c d) = d
evalFun2 IfLf          lf       lf       = lf  -- safe default (axIfLfLL)
evalFun2 IfLf          (nd _ _) lf       = lf  -- safe default (axIfLfNL)
evalFun2 TreeEq        a b = treeEqual a b
evalFun2 (RecP s)      a lf       = lf
evalFun2 (RecP s)      a (nd b1 b2) =
  evalFun2 s (nd a (nd b1 b2))
    (nd (evalFun2 (RecP s) a b1) (evalFun2 (RecP s) a b2))

------------------------------------------------------------------------
-- Spec type for stepT12 (Fun1 case).
--
-- StepT12Spec1 F i  bundles a proof-code Tree d and the Deriv that thmT(d)
-- decodes to the codeFormula of the canonical-input Theorem 12 equation.

StepT12Spec1 : Fun1 -> Tree -> Set
StepT12Spec1 F i =
  Sigma Tree (\ d ->
    Deriv (atomic (eqn (ap1 thmT (reify d))
                       (reify (codeFormula
                         (atomic (eqn (ap1 F (reify i))
                                       (reify (evalFun1 F i)))))))))

StepT12Spec2 : Fun2 -> Tree -> Tree -> Set
StepT12Spec2 G i j =
  Sigma Tree (\ d ->
    Deriv (atomic (eqn (ap1 thmT (reify d))
                       (reify (codeFormula
                         (atomic (eqn (ap2 G (reify i) (reify j))
                                       (reify (evalFun2 G i j)))))))))

------------------------------------------------------------------------
-- Case I (identity).
--
-- ap1 I (reify i) = reify i  by axI.
-- evalFun1 I i = i, so the spec's RHS is
--   reify (codeFormula (atomic (eqn (ap1 I (reify i)) (reify i)))) .
-- This matches  reify (outAxI (reify i))  exactly.
-- So Df = encAxI (reify i), proof = thmTDispAxI (reify i).

stepT12_I : (i : Tree) -> StepT12Spec1 I i
stepT12_I i = mkSigma (encAxI (reify i)) (thmTDispAxI (reify i))

------------------------------------------------------------------------
-- Case Z (constant zero).
--
-- ap1 Z (reify i) = O = reify lf  by axZ.
-- evalFun1 Z i = lf, so spec's RHS reduces to
--   reify (codeFormula (atomic (eqn (ap1 Z (reify i)) O))) .
-- This matches  reify (outAxZ (reify i))  exactly.

stepT12_Z : (i : Tree) -> StepT12Spec1 Z i
stepT12_Z i = mkSigma (encAxZ (reify i)) (thmTDispAxZ (reify i))

------------------------------------------------------------------------
-- Case Fst (with shape dispatch on i).
--
-- At i = lf:        ap1 Fst O = O                     (axFstLf safe-default).
--                    evalFun1 Fst lf = lf .  Use encAxFstLf.
-- At i = nd a b:    ap1 Fst (Pair (reify a) (reify b)) = reify a   (axFst).
--                    evalFun1 Fst (nd a b) = a .  Use encAxFst (reify a) (reify b).

stepT12_Fst : (i : Tree) -> StepT12Spec1 Fst i
stepT12_Fst lf       = mkSigma encAxFstLf thmTDispAxFstLf
stepT12_Fst (nd a b) = mkSigma (encAxFst (reify a) (reify b))
                                (thmTDispAxFst (reify a) (reify b))

------------------------------------------------------------------------
-- Case Snd (analogous to Fst).

stepT12_Snd : (i : Tree) -> StepT12Spec1 Snd i
stepT12_Snd lf       = mkSigma encAxSndLf thmTDispAxSndLf
stepT12_Snd (nd a b) = mkSigma (encAxSnd (reify a) (reify b))
                                (thmTDispAxSnd (reify a) (reify b))

------------------------------------------------------------------------
-- Case Comp f g (composite, takes sub-functor recursors).
--
-- Chain (per the user's reconstruction, plus the axComp step the
-- reconstruction omitted):
--   step1 :  ap1 (Comp f g) (reify i) = ap1 f (ap1 g (reify i))      -- axComp
--   step2 :  ap1 f (ap1 g (reify i)) = ap1 f (reify (evalFun1 g i))  -- cong1 f (rec_g)
--   step3 :  ap1 f (reify (evalFun1 g i)) = reify (evalFun1 f (evalFun1 g i))  -- rec_f
-- Composed via two parDispRuleTrans applications.

stepT12_Comp :
  (f g : Fun1)
  (rec_g : (j : Tree) -> StepT12Spec1 g j)
  (rec_f : (j : Tree) -> StepT12Spec1 f j)
  (i : Tree) -> StepT12Spec1 (Comp f g) i
stepT12_Comp f g rec_g rec_f i =
  let
    iT : Term
    iT = reify i

    g_at_i : StepT12Spec1 g i
    g_at_i = rec_g i

    d_g_tree : Tree
    d_g_tree = fst g_at_i

    d_g_proof : Deriv (atomic (eqn (ap1 thmT (reify d_g_tree))
                                    (reify (codeFormula
                                      (atomic (eqn (ap1 g iT)
                                                    (reify (evalFun1 g i))))))))
    d_g_proof = snd g_at_i

    eg_i : Term
    eg_i = reify (evalFun1 g i)

    f_at_g_i : StepT12Spec1 f (evalFun1 g i)
    f_at_g_i = rec_f (evalFun1 g i)

    d_f_tree : Tree
    d_f_tree = fst f_at_g_i

    d_f_proof : Deriv (atomic (eqn (ap1 thmT (reify d_f_tree))
                                    (reify (codeFormula
                                      (atomic (eqn (ap1 f eg_i)
                                                    (reify (evalFun1 f (evalFun1 g i)))))))))
    d_f_proof = snd f_at_g_i

    -- Step 1: encoded axComp at f, g, iT.
    step1 : Deriv (atomic (eqn (ap1 thmT (reify (encAxComp f g iT)))
                                (reify (outAxComp f g iT))))
    step1 = thmTDispAxComp f g iT

    -- Step 2: encoded cong1 f at d_g_tree, lifting d_g_proof.
    step2 : Deriv (atomic (eqn (ap1 thmT (reify (encCong1 f d_g_tree)))
                                (reify (outCong1 f (ap1 g iT) eg_i))))
    step2 = thmTDispCong1 f (ap1 g iT) eg_i d_g_tree d_g_proof

    -- Compose step1 + step2 via thmTDispRuleTrans.
    -- t = ap1 (Comp f g) iT, u = ap1 f (ap1 g iT), v = ap1 f eg_i.
    shape1 : Deriv (atomic (eqn (ap1 Fst (reify (encAxComp f g iT)))
                                 tagCode_axComp))
    shape1 = axFst tagCode_axComp _

    chain12 : Deriv (atomic (eqn
                (ap1 thmT (reify (encRuleTrans (encAxComp f g iT) (encCong1 f d_g_tree))))
                (reify (outRuleTrans (ap1 (Comp f g) iT) (ap1 f eg_i)))))
    chain12 = thmTDispRuleTrans
                (ap1 (Comp f g) iT) (ap1 f (ap1 g iT)) (ap1 f eg_i)
                (encAxComp f g iT) (encCong1 f d_g_tree)
                _ shape1 step1 step2

    -- Compose chain12 + d_f_proof via thmTDispRuleTrans.
    shape2 : Deriv (atomic (eqn
                (ap1 Fst (reify (encRuleTrans (encAxComp f g iT) (encCong1 f d_g_tree))))
                tagCode_ruleTrans))
    shape2 = axFst tagCode_ruleTrans _

    final : Deriv (atomic (eqn
                (ap1 thmT (reify
                  (encRuleTrans
                    (encRuleTrans (encAxComp f g iT) (encCong1 f d_g_tree))
                    d_f_tree)))
                (reify (outRuleTrans (ap1 (Comp f g) iT)
                                      (reify (evalFun1 f (evalFun1 g i)))))))
    final = thmTDispRuleTrans
              (ap1 (Comp f g) iT) (ap1 f eg_i) (reify (evalFun1 f (evalFun1 g i)))
              (encRuleTrans (encAxComp f g iT) (encCong1 f d_g_tree))
              d_f_tree
              _ shape2 chain12 d_f_proof

  in mkSigma
       (encRuleTrans
         (encRuleTrans (encAxComp f g iT) (encCong1 f d_g_tree))
         d_f_tree)
       final

------------------------------------------------------------------------
-- Cleaner architecture for the Rec case (and a template for all
-- remaining cases): build the BRA-Deriv directly by structural
-- recursion, then apply  encode  to lift to the doubly-encoded form.
--
-- This validates the user's reformulation at the actually-tricky case.
-- The pattern avoids per-case dispatcher composition (parDispRuleTrans,
-- parDispCong1, etc.) and instead uses Agda recursion + the existing
-- encode soundness internalisation.
--
-- Restricted to z = O (the typical usage in our codebase, including
-- thmT itself which is Rec O stepProto).  Handling general z requires
-- meta-evaluation of z's Term value, which is a side condition; for
-- z = O the side condition is automatic.

------------------------------------------------------------------------
-- BRA-Deriv version of Theorem 12 at f = Rec O s, by Tree-induction.
--
-- Takes a sub-functor recursor  rec_s : (i j : Tree) -> Deriv ...
-- (the BRA-Deriv version of Theorem 12 at  s : Fun2 ).

eval_correct_RecO :
  (s : Fun2) ->
  ((j k : Tree) ->
    Deriv (atomic (eqn (ap2 s (reify j) (reify k)) (reify (evalFun2 s j k))))) ->
  (i : Tree) ->
  Deriv (atomic (eqn (ap1 (Rec O s) (reify i))
                     (reify (evalFun1 (Rec O s) i))))
eval_correct_RecO s rec_s lf       = axRecLf O s
eval_correct_RecO s rec_s (nd a b) =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    raT : Term
    raT = reify (evalFun1 (Rec O s) a)

    rbT : Term
    rbT = reify (evalFun1 (Rec O s) b)

    -- Step 1: axRecNd at z = O, s, reify a, reify b.

    step1 : Deriv (atomic (eqn (ap1 (Rec O s) (ap2 Pair aT bT))
                               (ap2 s (ap2 Pair aT bT)
                                       (ap2 Pair (ap1 (Rec O s) aT)
                                                  (ap1 (Rec O s) bT)))))
    step1 = axRecNd O s aT bT

    -- Step 2: bridge the inner Pair via cross-IHs.

    ih_a : Deriv (atomic (eqn (ap1 (Rec O s) aT) raT))
    ih_a = eval_correct_RecO s rec_s a

    ih_b : Deriv (atomic (eqn (ap1 (Rec O s) bT) rbT))
    ih_b = eval_correct_RecO s rec_s b

    inner_pair_eq : Deriv (atomic (eqn
                      (ap2 Pair (ap1 (Rec O s) aT) (ap1 (Rec O s) bT))
                      (ap2 Pair raT rbT)))
    inner_pair_eq = ruleTrans (congL Pair (ap1 (Rec O s) bT) ih_a)
                              (congR Pair raT ih_b)

    step2 : Deriv (atomic (eqn
              (ap2 s (ap2 Pair aT bT)
                     (ap2 Pair (ap1 (Rec O s) aT) (ap1 (Rec O s) bT)))
              (ap2 s (ap2 Pair aT bT) (ap2 Pair raT rbT))))
    step2 = congR s (ap2 Pair aT bT) inner_pair_eq

    -- Step 3: rec_s applied at canonical (nd a b, nd ra rb).
    -- reify (nd a b) = ap2 Pair (reify a) (reify b) definitionally.
    -- reify (nd ra rb) = ap2 Pair raT rbT definitionally.
    -- So step3 has the same syntactic form as step2's RHS.

    step3 : Deriv (atomic (eqn (ap2 s (ap2 Pair aT bT) (ap2 Pair raT rbT))
                                (reify (evalFun2 s (nd a b)
                                          (nd (evalFun1 (Rec O s) a)
                                              (evalFun1 (Rec O s) b))))))
    step3 = rec_s (nd a b) (nd (evalFun1 (Rec O s) a) (evalFun1 (Rec O s) b))

  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- stepT12_RecO : the doubly-encoded Theorem 12 at f = Rec O s,
-- via  encode  applied to  eval_correct_RecO .

stepT12_RecO :
  (s : Fun2) ->
  ((j k : Tree) ->
    Deriv (atomic (eqn (ap2 s (reify j) (reify k)) (reify (evalFun2 s j k))))) ->
  (i : Tree) -> StepT12Spec1 (Rec O s) i
stepT12_RecO s rec_s i =
  encode (atomic (eqn (ap1 (Rec O s) (reify i))
                       (reify (evalFun1 (Rec O s) i))))
         (eval_correct_RecO s rec_s i)

------------------------------------------------------------------------
-- Architectural test:  apply  stepT12_RecO  at  s = Pair  and concrete
-- canonical inputs, with  rec_Pair = axRefl _  (since
--   ap2 Pair (reify i) (reify j)  is definitionally equal to  reify (nd i j) ,
-- the s-evaluator at Pair is just reflexivity).
--
-- This validates the full chain end-to-end:
--   eval_correct_RecO recursion + encode + stepT12_RecO assembly
-- producing a closed Sigma at concrete inputs.

rec_Pair : (j k : Tree) ->
  Deriv (atomic (eqn (ap2 Pair (reify j) (reify k)) (reify (evalFun2 Pair j k))))
rec_Pair j k = axRefl (ap2 Pair (reify j) (reify k))

test_RecO_Pair_lf : StepT12Spec1 (Rec O Pair) lf
test_RecO_Pair_lf = stepT12_RecO Pair rec_Pair lf

test_RecO_Pair_nd_lf_lf : StepT12Spec1 (Rec O Pair) (nd lf lf)
test_RecO_Pair_nd_lf_lf = stepT12_RecO Pair rec_Pair (nd lf lf)

test_RecO_Pair_nd_nested : StepT12Spec1 (Rec O Pair) (nd (nd lf lf) lf)
test_RecO_Pair_nd_nested = stepT12_RecO Pair rec_Pair (nd (nd lf lf) lf)

------------------------------------------------------------------------
-- Fun2 atomic cases of stepT12 (Theorem 12).
--
-- Each non-recursive Fun2 case is one-line: pick the corresponding
-- thmTDispAxX dispatcher whose outAxX equation matches  evalFun2 G i j
-- definitionally, and bundle (encAxX..., thmTDispAxX...) as a Sigma.
--
-- Composite Fun2 cases (Lift, Post, Fan) require sub-functor recursion
-- chained through parDispAx + parDispCong* + parDispRuleTrans, like
-- stepT12_Comp on the Fun1 side.  Deferred to the next session.
--
-- TreeEq's NN case (diagonal recursion on tree-pair size) is the open
-- architectural piece (no Guard analog, see BRA/THM12-TREEEQ-NECESSITY.md).
-- Deferred — it requires a separate evaluator outside the mutual
-- evalFun1/evalFun2 group to satisfy Agda's termination checker.

------------------------------------------------------------------------
-- Pair (no Fun2 axiom needed; reflexivity).
--
-- evalFun2 Pair i j = nd i j ; reify (nd i j) = ap2 Pair (reify i) (reify j)
-- definitionally.  So the spec's equation is  eqn t t  for
-- t = ap2 Pair (reify i) (reify j) — pure reflexivity.

stepT12_Pair : (i j : Tree) -> StepT12Spec2 Pair i j
stepT12_Pair i j =
  mkSigma (encAxRefl (ap2 Pair (reify i) (reify j)))
          (thmTDispAxRefl (ap2 Pair (reify i) (reify j)))

------------------------------------------------------------------------
-- Const.
--
-- evalFun2 Const i j = i.  outAxConst iT jT = code(eqn (ap2 Const iT jT) iT).
-- Direct match.

stepT12_Const : (i j : Tree) -> StepT12Spec2 Const i j
stepT12_Const i j =
  mkSigma (encAxConst (reify i) (reify j))
          (thmTDispAxConst (reify i) (reify j))

------------------------------------------------------------------------
-- IfLf (shape-dispatched on (i, j)):
--   lf      , nd c d  : axIfLfL  ; evalFun2 IfLf lf       (nd c d) = c .
--   nd a b  , nd c d  : axIfLfN  ; evalFun2 IfLf (nd a b) (nd c d) = d .
--   lf      , lf      : axIfLfLL ; safe-default lf .
--   nd a b  , lf      : axIfLfNL ; safe-default lf .
--
-- Each row matches the corresponding outAxIfLf* equation definitionally.

stepT12_IfLf : (i j : Tree) -> StepT12Spec2 IfLf i j
stepT12_IfLf lf       (nd c d) =
  mkSigma (encAxIfLfL (reify c) (reify d))
          (thmTDispAxIfLfL (reify c) (reify d))
stepT12_IfLf (nd a b) (nd c d) =
  mkSigma (encAxIfLfN (reify a) (reify b) (reify c) (reify d))
          (thmTDispAxIfLfN (reify a) (reify b) (reify c) (reify d))
stepT12_IfLf lf       lf       =
  mkSigma encAxIfLfLL thmTDispAxIfLfLL
stepT12_IfLf (nd a b) lf       =
  mkSigma (encAxIfLfNL (reify a) (reify b))
          (thmTDispAxIfLfNL (reify a) (reify b))

------------------------------------------------------------------------
-- TreeEq (3 of 4 shape cases — TreeEqNN deferred per the canonical-input
-- plan; see BRA/THM12-TREEEQ-NECESSITY.md):
--   lf      , lf      : axTreeEqLL ; evalFun2 TreeEq lf       lf       = lf .
--   lf      , nd a b  : axTreeEqLN ; evalFun2 TreeEq lf       (nd a b) = nd lf lf .
--   nd a b  , lf      : axTreeEqNL ; evalFun2 TreeEq (nd a b) lf       = nd lf lf .
--
-- Provided as 3 individual per-shape lemmas (NOT a unified dispatcher),
-- so the file remains hole-free.  When TreeEqNN is built (via separate
-- evaluator outside the mutual evalFun1/evalFun2 group), a unified
-- stepT12_TreeEq can be assembled atop these three plus the NN case.

stepT12_TreeEqLL : StepT12Spec2 TreeEq lf lf
stepT12_TreeEqLL = mkSigma encAxTreeEqLL thmTDispAxTreeEqLL

stepT12_TreeEqLN : (a b : Tree) -> StepT12Spec2 TreeEq lf (nd a b)
stepT12_TreeEqLN a b =
  mkSigma (encAxTreeEqLN (reify a) (reify b))
          (thmTDispAxTreeEqLN (reify a) (reify b))

stepT12_TreeEqNL : (a b : Tree) -> StepT12Spec2 TreeEq (nd a b) lf
stepT12_TreeEqNL a b =
  mkSigma (encAxTreeEqNL (reify a) (reify b))
          (thmTDispAxTreeEqNL (reify a) (reify b))

------------------------------------------------------------------------
-- Composite Fun2 cases of stepT12 (Theorem 12).
--
-- Each takes one or more sub-functor recursors and chains
--   axX  +  cong* over rec_sub  +  rec_outer
-- via thmTDispRuleTrans, exactly like  stepT12_Comp  on the Fun1 side.
--
-- Lift  is a 2-step chain (single ruleTrans):     axLift + rec_f.
-- Post  is a 3-step chain (two ruleTrans's):       axPost + cong1 over rec_h + rec_f.
-- Fan   is a 4-step chain (three ruleTrans's):     axFan  + congL over rec_h1 + congR over rec_h2 + rec_h.
-- Comp2 is a 4-step chain (three ruleTrans's), Fun1-side analog of Fan:
--                                                  axComp2 + congL over rec_f + congR over rec_g + rec_h.

------------------------------------------------------------------------
-- Lift f: ap2 (Lift f) aT bT  --axLift-->  ap1 f aT  --rec_f-->  reify (evalFun1 f a) .
--
-- evalFun2 (Lift f) a b = evalFun1 f a, so the b-input is unused at the
-- spec level (b appears only inside the LHS ap2 (Lift f) aT bT).

stepT12_Lift :
  (f : Fun1)
  (rec_f : (j : Tree) -> StepT12Spec1 f j)
  (a b : Tree) -> StepT12Spec2 (Lift f) a b
stepT12_Lift f rec_f a b =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    f_at_a : StepT12Spec1 f a
    f_at_a = rec_f a

    d_f_tree : Tree
    d_f_tree = fst f_at_a

    d_f_proof : Deriv (atomic (eqn (ap1 thmT (reify d_f_tree))
                                    (reify (codeFormula
                                      (atomic (eqn (ap1 f aT)
                                                    (reify (evalFun1 f a))))))))
    d_f_proof = snd f_at_a

    -- step1: encoded axLift.
    step1 : Deriv (atomic (eqn (ap1 thmT (reify (encAxLift f aT bT)))
                                (reify (outAxLift f aT bT))))
    step1 = thmTDispAxLift f aT bT

    -- shape for ruleTrans chaining encAxLift + d_f_tree.
    shape : Deriv (atomic (eqn (ap1 Fst (reify (encAxLift f aT bT)))
                                tagCode_axLift))
    shape = axFst tagCode_axLift _

    -- final: thmTDispRuleTrans at
    --   t = ap2 (Lift f) aT bT, u = ap1 f aT, v = reify (evalFun1 f a).
    final : Deriv (atomic (eqn
              (ap1 thmT (reify (encRuleTrans (encAxLift f aT bT) d_f_tree)))
              (reify (outRuleTrans (ap2 (Lift f) aT bT)
                                    (reify (evalFun1 f a))))))
    final = thmTDispRuleTrans
              (ap2 (Lift f) aT bT) (ap1 f aT) (reify (evalFun1 f a))
              (encAxLift f aT bT) d_f_tree
              _ shape step1 d_f_proof
  in mkSigma (encRuleTrans (encAxLift f aT bT) d_f_tree) final

------------------------------------------------------------------------
-- Post f h: ap2 (Post f h) aT bT  --axPost-->  ap1 f (ap2 h aT bT)
--                                  --cong1 f over rec_h-->  ap1 f (reify (evalFun2 h a b))
--                                  --rec_f-->  reify (evalFun1 f (evalFun2 h a b)) .

stepT12_Post :
  (f : Fun1) (h : Fun2)
  (rec_h : (j k : Tree) -> StepT12Spec2 h j k)
  (rec_f : (j : Tree) -> StepT12Spec1 f j)
  (a b : Tree) -> StepT12Spec2 (Post f h) a b
stepT12_Post f h rec_h rec_f a b =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    h_at_ab : StepT12Spec2 h a b
    h_at_ab = rec_h a b

    d_h_tree : Tree
    d_h_tree = fst h_at_ab

    d_h_proof : Deriv (atomic (eqn (ap1 thmT (reify d_h_tree))
                                    (reify (codeFormula
                                      (atomic (eqn (ap2 h aT bT)
                                                    (reify (evalFun2 h a b))))))))
    d_h_proof = snd h_at_ab

    eh_ab : Term
    eh_ab = reify (evalFun2 h a b)

    f_at_h_ab : StepT12Spec1 f (evalFun2 h a b)
    f_at_h_ab = rec_f (evalFun2 h a b)

    d_f_tree : Tree
    d_f_tree = fst f_at_h_ab

    d_f_proof : Deriv (atomic (eqn (ap1 thmT (reify d_f_tree))
                                    (reify (codeFormula
                                      (atomic (eqn (ap1 f eh_ab)
                                                    (reify (evalFun1 f (evalFun2 h a b)))))))))
    d_f_proof = snd f_at_h_ab

    -- step1: encoded axPost.
    step1 : Deriv (atomic (eqn (ap1 thmT (reify (encAxPost f h aT bT)))
                                (reify (outAxPost f h aT bT))))
    step1 = thmTDispAxPost f h aT bT

    -- step2: encoded cong1 f over d_h_tree.
    step2 : Deriv (atomic (eqn (ap1 thmT (reify (encCong1 f d_h_tree)))
                                (reify (outCong1 f (ap2 h aT bT) eh_ab))))
    step2 = thmTDispCong1 f (ap2 h aT bT) eh_ab d_h_tree d_h_proof

    -- shape1: ruleTrans chaining encAxPost + encCong1.
    shape1 : Deriv (atomic (eqn (ap1 Fst (reify (encAxPost f h aT bT)))
                                 tagCode_axPost))
    shape1 = axFst tagCode_axPost _

    -- chain12: trans(step1, step2) at (ap2 (Post f h) aT bT, ap1 f (ap2 h aT bT), ap1 f eh_ab).
    chain12 : Deriv (atomic (eqn
                (ap1 thmT (reify (encRuleTrans (encAxPost f h aT bT) (encCong1 f d_h_tree))))
                (reify (outRuleTrans (ap2 (Post f h) aT bT) (ap1 f eh_ab)))))
    chain12 = thmTDispRuleTrans
                (ap2 (Post f h) aT bT) (ap1 f (ap2 h aT bT)) (ap1 f eh_ab)
                (encAxPost f h aT bT) (encCong1 f d_h_tree)
                _ shape1 step1 step2

    -- shape2: ruleTrans chaining chain12 + d_f.
    shape2 : Deriv (atomic (eqn
                (ap1 Fst (reify (encRuleTrans (encAxPost f h aT bT) (encCong1 f d_h_tree))))
                tagCode_ruleTrans))
    shape2 = axFst tagCode_ruleTrans _

    final : Deriv (atomic (eqn
                (ap1 thmT (reify
                  (encRuleTrans
                    (encRuleTrans (encAxPost f h aT bT) (encCong1 f d_h_tree))
                    d_f_tree)))
                (reify (outRuleTrans (ap2 (Post f h) aT bT)
                                      (reify (evalFun1 f (evalFun2 h a b)))))))
    final = thmTDispRuleTrans
              (ap2 (Post f h) aT bT) (ap1 f eh_ab)
              (reify (evalFun1 f (evalFun2 h a b)))
              (encRuleTrans (encAxPost f h aT bT) (encCong1 f d_h_tree))
              d_f_tree
              _ shape2 chain12 d_f_proof
  in mkSigma
       (encRuleTrans
         (encRuleTrans (encAxPost f h aT bT) (encCong1 f d_h_tree))
         d_f_tree)
       final

------------------------------------------------------------------------
-- Rich-spec variants (with shape proof) for composite cases that need
-- congL / congR.
--
-- The thmTDispCongL / thmTDispCongR dispatchers require, in addition to
-- the equation Deriv on the inner sub-proof code y_h, a shape derivation
--   Deriv (atomic (eqn (ap1 Fst (reify y_h)) (ap2 Pair O y_h')))
-- exhibiting that  y_h  is encoded with a non-zero top tag.  When the
-- inner y_h comes from a sub-recursor's result, the caller cannot supply
-- this shape without knowing the recursor's specific top tag.
--
-- Rather than thread shape arguments through every recursor type, we
-- piggyback on the existing  encodeRich  infrastructure: each composite
-- case can be expressed as a pure BRA-level chain of axioms / cong / trans,
-- and  encodeRich  (already proved sound elsewhere in this codebase) does
-- ALL the encoding work — including producing the shape proof.
--
-- This dramatically simplifies Fan and Comp2 (and is also a cleaner
-- alternative for Lift and Post, though the manual versions above are
-- preserved for continuity with stepT12_Comp).

StepT12Rich1 : Fun1 -> Tree -> Set
StepT12Rich1 F i =
  Sigma Tree (\ y ->
    Sigma Term (\ y' ->
      Sigma (Deriv (atomic (eqn (ap1 Fst (reify y)) (ap2 Pair O y'))))
            (\ _ -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                        (reify (codeFormula
                                          (atomic (eqn (ap1 F (reify i))
                                                        (reify (evalFun1 F i)))))))))))

StepT12Rich2 : Fun2 -> Tree -> Tree -> Set
StepT12Rich2 G i j =
  Sigma Tree (\ y ->
    Sigma Term (\ y' ->
      Sigma (Deriv (atomic (eqn (ap1 Fst (reify y)) (ap2 Pair O y'))))
            (\ _ -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                        (reify (codeFormula
                                          (atomic (eqn (ap2 G (reify i) (reify j))
                                                        (reify (evalFun2 G i j)))))))))))

-- BRA-Deriv recursor types (input form for the rich composite cases).

EvalCorrect1 : Fun1 -> Tree -> Set
EvalCorrect1 F i =
  Deriv (atomic (eqn (ap1 F (reify i)) (reify (evalFun1 F i))))

EvalCorrect2 : Fun2 -> Tree -> Tree -> Set
EvalCorrect2 G i j =
  Deriv (atomic (eqn (ap2 G (reify i) (reify j)) (reify (evalFun2 G i j))))

------------------------------------------------------------------------
-- Fan h1 h2 h: 4-step BRA-level chain
--   ap2 (Fan h1 h2 h) aT bT
--      --axFan-->          ap2 h (ap2 h1 aT bT) (ap2 h2 aT bT)
--      --congL h via rec_h1-->  ap2 h (reify (evalFun2 h1 a b)) (ap2 h2 aT bT)
--      --congR h via rec_h2-->  ap2 h (reify (evalFun2 h1 a b)) (reify (evalFun2 h2 a b))
--      --rec_h-->          reify (evalFun2 h (evalFun2 h1 a b) (evalFun2 h2 a b))
-- = reify (evalFun2 (Fan h1 h2 h) a b) .

stepT12_Fan_rich :
  (h1 h2 h : Fun2)
  (rec_h1 : (j k : Tree) -> EvalCorrect2 h1 j k)
  (rec_h2 : (j k : Tree) -> EvalCorrect2 h2 j k)
  (rec_h  : (j k : Tree) -> EvalCorrect2 h  j k)
  (a b : Tree) -> StepT12Rich2 (Fan h1 h2 h) a b
stepT12_Fan_rich h1 h2 h rec_h1 rec_h2 rec_h a b =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    e1 : Tree
    e1 = evalFun2 h1 a b

    e2 : Tree
    e2 = evalFun2 h2 a b

    step1 : Deriv (atomic (eqn (ap2 (Fan h1 h2 h) aT bT)
                                (ap2 h (ap2 h1 aT bT) (ap2 h2 aT bT))))
    step1 = axFan h1 h2 h aT bT

    step2 : Deriv (atomic (eqn (ap2 h (ap2 h1 aT bT)        (ap2 h2 aT bT))
                                (ap2 h (reify e1)            (ap2 h2 aT bT))))
    step2 = congL h (ap2 h2 aT bT) (rec_h1 a b)

    step3 : Deriv (atomic (eqn (ap2 h (reify e1) (ap2 h2 aT bT))
                                (ap2 h (reify e1) (reify e2))))
    step3 = congR h (reify e1) (rec_h2 a b)

    step4 : Deriv (atomic (eqn (ap2 h (reify e1) (reify e2))
                                (reify (evalFun2 h e1 e2))))
    step4 = rec_h e1 e2

    bra : Deriv (atomic (eqn (ap2 (Fan h1 h2 h) aT bT)
                              (reify (evalFun2 (Fan h1 h2 h) a b))))
    bra = ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))

  in encodeRich
       (atomic (eqn (ap2 (Fan h1 h2 h) aT bT)
                     (reify (evalFun2 (Fan h1 h2 h) a b))))
       bra

------------------------------------------------------------------------
-- Comp2 h f g (Fun1-side analog of Fan, with i instead of (a, b)):
--   ap1 (Comp2 h f g) iT
--      --axComp2-->         ap2 h (ap1 f iT) (ap1 g iT)
--      --congL h via rec_f-->  ap2 h (reify (evalFun1 f i)) (ap1 g iT)
--      --congR h via rec_g-->  ap2 h (reify (evalFun1 f i)) (reify (evalFun1 g i))
--      --rec_h-->           reify (evalFun2 h (evalFun1 f i) (evalFun1 g i))
-- = reify (evalFun1 (Comp2 h f g) i) .

stepT12_Comp2_rich :
  (h : Fun2) (f g : Fun1)
  (rec_f : (j : Tree) -> EvalCorrect1 f j)
  (rec_g : (j : Tree) -> EvalCorrect1 g j)
  (rec_h : (j k : Tree) -> EvalCorrect2 h j k)
  (i : Tree) -> StepT12Rich1 (Comp2 h f g) i
stepT12_Comp2_rich h f g rec_f rec_g rec_h i =
  let
    iT : Term
    iT = reify i

    ef : Tree
    ef = evalFun1 f i

    eg : Tree
    eg = evalFun1 g i

    step1 : Deriv (atomic (eqn (ap1 (Comp2 h f g) iT)
                                (ap2 h (ap1 f iT) (ap1 g iT))))
    step1 = axComp2 h f g iT

    step2 : Deriv (atomic (eqn (ap2 h (ap1 f iT)   (ap1 g iT))
                                (ap2 h (reify ef)   (ap1 g iT))))
    step2 = congL h (ap1 g iT) (rec_f i)

    step3 : Deriv (atomic (eqn (ap2 h (reify ef) (ap1 g iT))
                                (ap2 h (reify ef) (reify eg))))
    step3 = congR h (reify ef) (rec_g i)

    step4 : Deriv (atomic (eqn (ap2 h (reify ef) (reify eg))
                                (reify (evalFun2 h ef eg))))
    step4 = rec_h ef eg

    bra : Deriv (atomic (eqn (ap1 (Comp2 h f g) iT)
                              (reify (evalFun1 (Comp2 h f g) i))))
    bra = ruleTrans step1 (ruleTrans step2 (ruleTrans step3 step4))

  in encodeRich
       (atomic (eqn (ap1 (Comp2 h f g) iT)
                     (reify (evalFun1 (Comp2 h f g) i))))
       bra

------------------------------------------------------------------------
-- Generalised Rec: parametric over z = reify zT for any Tree zT.
--
-- The original  evalFun1 (Rec z s) lf = lf  is correct only when z = O.
-- For arbitrary canonical z, we need a separate evaluator that takes
-- the underlying  zT : Tree  explicitly.  evalFun1Z does that.

evalFun1Z : Tree -> Fun2 -> Tree -> Tree
evalFun1Z zT s lf       = zT
evalFun1Z zT s (nd a b) =
  evalFun2 s (nd a b)
    (nd (evalFun1Z zT s a) (evalFun1Z zT s b))

------------------------------------------------------------------------
-- BRA-Deriv level: Theorem 12 at f = Rec (reify zT) s, by Tree-induction on i.
--
-- Generalises  eval_correct_RecO  (which is the zT = lf case).
-- Takes a sub-functor recursor for s.

eval_correct_RecZ :
  (zT : Tree)
  (s : Fun2) ->
  ((j k : Tree) -> EvalCorrect2 s j k) ->
  (i : Tree) ->
  Deriv (atomic (eqn (ap1 (Rec (reify zT) s) (reify i))
                     (reify (evalFun1Z zT s i))))
eval_correct_RecZ zT s rec_s lf       = axRecLf (reify zT) s
eval_correct_RecZ zT s rec_s (nd a b) =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    raT : Term
    raT = reify (evalFun1Z zT s a)

    rbT : Term
    rbT = reify (evalFun1Z zT s b)

    -- Step 1: axRecNd at z = reify zT.
    step1 : Deriv (atomic (eqn (ap1 (Rec (reify zT) s) (ap2 Pair aT bT))
                               (ap2 s (ap2 Pair aT bT)
                                       (ap2 Pair (ap1 (Rec (reify zT) s) aT)
                                                  (ap1 (Rec (reify zT) s) bT)))))
    step1 = axRecNd (reify zT) s aT bT

    -- IHs at a, b.
    ih_a : Deriv (atomic (eqn (ap1 (Rec (reify zT) s) aT) raT))
    ih_a = eval_correct_RecZ zT s rec_s a

    ih_b : Deriv (atomic (eqn (ap1 (Rec (reify zT) s) bT) rbT))
    ih_b = eval_correct_RecZ zT s rec_s b

    -- Step 2: bridge the inner Pair via the IHs.
    inner_pair_eq : Deriv (atomic (eqn
                      (ap2 Pair (ap1 (Rec (reify zT) s) aT) (ap1 (Rec (reify zT) s) bT))
                      (ap2 Pair raT rbT)))
    inner_pair_eq = ruleTrans (congL Pair (ap1 (Rec (reify zT) s) bT) ih_a)
                              (congR Pair raT ih_b)

    step2 : Deriv (atomic (eqn
              (ap2 s (ap2 Pair aT bT)
                     (ap2 Pair (ap1 (Rec (reify zT) s) aT) (ap1 (Rec (reify zT) s) bT)))
              (ap2 s (ap2 Pair aT bT) (ap2 Pair raT rbT))))
    step2 = congR s (ap2 Pair aT bT) inner_pair_eq

    -- Step 3: rec_s at canonical inputs (nd a b, nd ra rb).
    -- reify (nd a b) = ap2 Pair aT bT and reify (nd ra rb) = ap2 Pair raT rbT,
    -- so step3's LHS matches step2's RHS definitionally.
    step3 : Deriv (atomic (eqn (ap2 s (ap2 Pair aT bT) (ap2 Pair raT rbT))
                                (reify (evalFun2 s (nd a b)
                                          (nd (evalFun1Z zT s a)
                                              (evalFun1Z zT s b))))))
    step3 = rec_s (nd a b) (nd (evalFun1Z zT s a) (evalFun1Z zT s b))

  in ruleTrans step1 (ruleTrans step2 step3)

------------------------------------------------------------------------
-- Rich-spec for parametric Rec:
--
-- StepT12RichRecZ zT s i  is StepT12Rich1 (Rec (reify zT) s) i specialised
-- so that the inner equation uses evalFun1Z (the parametric evaluator).
--
-- Indexed by zT explicitly because  evalFun1 (Rec (reify zT) s) i  does
-- NOT compute correctly for non-canonical z; we use evalFun1Z instead.

StepT12RichRecZ : Tree -> Fun2 -> Tree -> Set
StepT12RichRecZ zT s i =
  Sigma Tree (\ y ->
    Sigma Term (\ y' ->
      Sigma (Deriv (atomic (eqn (ap1 Fst (reify y)) (ap2 Pair O y'))))
            (\ _ -> Deriv (atomic (eqn (ap1 thmT (reify y))
                                        (reify (codeFormula
                                          (atomic (eqn (ap1 (Rec (reify zT) s) (reify i))
                                                        (reify (evalFun1Z zT s i)))))))))))

stepT12_RecZ_rich :
  (zT : Tree)
  (s : Fun2) ->
  ((j k : Tree) -> EvalCorrect2 s j k) ->
  (i : Tree) -> StepT12RichRecZ zT s i
stepT12_RecZ_rich zT s rec_s i =
  encodeRich
    (atomic (eqn (ap1 (Rec (reify zT) s) (reify i))
                  (reify (evalFun1Z zT s i))))
    (eval_correct_RecZ zT s rec_s i)

------------------------------------------------------------------------
-- BRA-Deriv API: per-case  EvalCorrect{1,2}  recursors.
--
-- Once these are in hand, every  stepT12_X_rich  collapses to
--   encodeRich  <eq>  (evalCorrect_X ...)
-- and downstream assembly (e.g., Th14-at) can compose them at the
-- BRA-Deriv level without re-deriving the chain.

------------------------------------------------------------------------
-- Atomic Fun1 EvalCorrect helpers.
--
-- Each is a one-line BRA-axiom application matching evalFun1's reduct.

evalCorrect_I : (i : Tree) -> EvalCorrect1 I i
evalCorrect_I i = axI (reify i)

evalCorrect_Z : (i : Tree) -> EvalCorrect1 Z i
evalCorrect_Z i = axZ (reify i)

evalCorrect_Fst : (i : Tree) -> EvalCorrect1 Fst i
evalCorrect_Fst lf       = axFstLf
evalCorrect_Fst (nd a b) = axFst (reify a) (reify b)

evalCorrect_Snd : (i : Tree) -> EvalCorrect1 Snd i
evalCorrect_Snd lf       = axSndLf
evalCorrect_Snd (nd a b) = axSnd (reify a) (reify b)

------------------------------------------------------------------------
-- Atomic Fun2 EvalCorrect helpers.

evalCorrect_Pair : (i j : Tree) -> EvalCorrect2 Pair i j
evalCorrect_Pair i j = axRefl (ap2 Pair (reify i) (reify j))

evalCorrect_Const : (i j : Tree) -> EvalCorrect2 Const i j
evalCorrect_Const i j = axConst (reify i) (reify j)

------------------------------------------------------------------------
-- IfLf: shape-dispatched on (i, j); all 4 cases have BRA axioms,
-- so rec_IfLf is total over (i, j).

evalCorrect_IfLf : (i j : Tree) -> EvalCorrect2 IfLf i j
evalCorrect_IfLf lf       (nd c d) = axIfLfL  (reify c) (reify d)
evalCorrect_IfLf (nd a b) (nd c d) = axIfLfN  (reify a) (reify b) (reify c) (reify d)
evalCorrect_IfLf lf       lf       = axIfLfLL
evalCorrect_IfLf (nd a b) lf       = axIfLfNL (reify a) (reify b)

------------------------------------------------------------------------
-- TreeEq: total over (a, b), including the NN case.
--
-- LL/LN/NL: direct from BRA axioms.
-- NN: axTreeEqNN reduces  ap2 TreeEq (Pair a1 a2) (Pair b1 b2)  to
--   ap2 IfLf (TreeEq a1 b1) (Pair (TreeEq a2 b2) (Pair O O)) ;
-- recursive IHs at (a1, b1) and (a2, b2) replace the inner TreeEqs with
-- reify of treeEqual ; finalize_at then case-splits on the shape of
-- treeEqual a1 b1  to invoke axIfLfL or axIfLfN.
--
-- finalize_at is a separate helper because it pattern-matches on the
-- runtime value  treeEqual a1 b1  (not on a static Fun2 or shape of
-- (a1,a2,b1,b2)), so it can't live inside the recursion on (a, b).

finalize_at : (eqv mid : Tree) ->
  Deriv (atomic (eqn (ap2 IfLf (reify eqv)
                              (ap2 Pair (reify mid) (ap2 Pair O O)))
                     (reify (combineEq eqv mid))))
finalize_at lf       mid = axIfLfL  (reify mid) (ap2 Pair O O)
finalize_at (nd c d) mid = axIfLfN  (reify c) (reify d)
                                    (reify mid) (ap2 Pair O O)

evalCorrect_TreeEq : (a b : Tree) -> EvalCorrect2 TreeEq a b
evalCorrect_TreeEq lf       lf       = axTreeEqLL
evalCorrect_TreeEq lf       (nd b1 b2) = axTreeEqLN (reify b1) (reify b2)
evalCorrect_TreeEq (nd a1 a2) lf      = axTreeEqNL (reify a1) (reify a2)
evalCorrect_TreeEq (nd a1 a2) (nd b1 b2) =
  let
    a1T : Term
    a1T = reify a1

    a2T : Term
    a2T = reify a2

    b1T : Term
    b1T = reify b1

    b2T : Term
    b2T = reify b2

    e1 : Tree
    e1 = treeEqual a1 b1

    e2 : Tree
    e2 = treeEqual a2 b2

    -- Step 1: axTreeEqNN.
    s1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair a1T a2T) (ap2 Pair b1T b2T))
                             (ap2 IfLf (ap2 TreeEq a1T b1T)
                                       (ap2 Pair (ap2 TreeEq a2T b2T)
                                                 (ap2 Pair O O)))))
    s1 = axTreeEqNN a1T a2T b1T b2T

    -- IH on (a1, b1): TreeEq a1T b1T = reify e1.
    ih1 : Deriv (atomic (eqn (ap2 TreeEq a1T b1T) (reify e1)))
    ih1 = evalCorrect_TreeEq a1 b1

    -- IH on (a2, b2): TreeEq a2T b2T = reify e2.
    ih2 : Deriv (atomic (eqn (ap2 TreeEq a2T b2T) (reify e2)))
    ih2 = evalCorrect_TreeEq a2 b2

    -- Step 2: substitute IH-1 inside IfLf's first slot via congL IfLf.
    s2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq a1T b1T)
                                       (ap2 Pair (ap2 TreeEq a2T b2T)
                                                 (ap2 Pair O O)))
                             (ap2 IfLf (reify e1)
                                       (ap2 Pair (ap2 TreeEq a2T b2T)
                                                 (ap2 Pair O O)))))
    s2 = congL IfLf (ap2 Pair (ap2 TreeEq a2T b2T) (ap2 Pair O O)) ih1

    -- Step 3a: substitute IH-2 inside the inner Pair's first slot via congL Pair.
    s3a : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq a2T b2T) (ap2 Pair O O))
                              (ap2 Pair (reify e2)            (ap2 Pair O O))))
    s3a = congL Pair (ap2 Pair O O) ih2

    -- Step 3: lift through IfLf's second slot via congR IfLf.
    s3 : Deriv (atomic (eqn (ap2 IfLf (reify e1) (ap2 Pair (ap2 TreeEq a2T b2T) (ap2 Pair O O)))
                             (ap2 IfLf (reify e1) (ap2 Pair (reify e2) (ap2 Pair O O)))))
    s3 = congR IfLf (reify e1) s3a

    -- Step 4: case-split on treeEqual a1 b1 (= e1) via finalize_at to evaluate IfLf.
    s4 : Deriv (atomic (eqn (ap2 IfLf (reify e1) (ap2 Pair (reify e2) (ap2 Pair O O)))
                             (reify (combineEq e1 e2))))
    s4 = finalize_at e1 e2

  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- Composite Fun1/Fun2 EvalCorrect helpers.
--
-- Each chains  ax_X  with  cong*  over sub-recursors and a final sub-
-- recursor application.  Same chain as the rich-spec versions above,
-- but at BRA-Deriv level (no encodeRich lift).

evalCorrect_Comp :
  (f g : Fun1)
  (rec_f : (j : Tree) -> EvalCorrect1 f j)
  (rec_g : (j : Tree) -> EvalCorrect1 g j)
  (i : Tree) -> EvalCorrect1 (Comp f g) i
evalCorrect_Comp f g rec_f rec_g i =
  let
    iT : Term
    iT = reify i

    s1 : Deriv (atomic (eqn (ap1 (Comp f g) iT) (ap1 f (ap1 g iT))))
    s1 = axComp f g iT

    s2 : Deriv (atomic (eqn (ap1 f (ap1 g iT)) (ap1 f (reify (evalFun1 g i)))))
    s2 = cong1 f (rec_g i)

    s3 : Deriv (atomic (eqn (ap1 f (reify (evalFun1 g i)))
                             (reify (evalFun1 f (evalFun1 g i)))))
    s3 = rec_f (evalFun1 g i)
  in ruleTrans s1 (ruleTrans s2 s3)

evalCorrect_Comp2 :
  (h : Fun2) (f g : Fun1)
  (rec_f : (j : Tree) -> EvalCorrect1 f j)
  (rec_g : (j : Tree) -> EvalCorrect1 g j)
  (rec_h : (j k : Tree) -> EvalCorrect2 h j k)
  (i : Tree) -> EvalCorrect1 (Comp2 h f g) i
evalCorrect_Comp2 h f g rec_f rec_g rec_h i =
  let
    iT : Term
    iT = reify i

    ef : Tree
    ef = evalFun1 f i

    eg : Tree
    eg = evalFun1 g i

    s1 : Deriv (atomic (eqn (ap1 (Comp2 h f g) iT)
                             (ap2 h (ap1 f iT) (ap1 g iT))))
    s1 = axComp2 h f g iT

    s2 : Deriv (atomic (eqn (ap2 h (ap1 f iT) (ap1 g iT))
                             (ap2 h (reify ef) (ap1 g iT))))
    s2 = congL h (ap1 g iT) (rec_f i)

    s3 : Deriv (atomic (eqn (ap2 h (reify ef) (ap1 g iT))
                             (ap2 h (reify ef) (reify eg))))
    s3 = congR h (reify ef) (rec_g i)

    s4 : Deriv (atomic (eqn (ap2 h (reify ef) (reify eg))
                             (reify (evalFun2 h ef eg))))
    s4 = rec_h ef eg
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

evalCorrect_Lift :
  (f : Fun1)
  (rec_f : (j : Tree) -> EvalCorrect1 f j)
  (a b : Tree) -> EvalCorrect2 (Lift f) a b
evalCorrect_Lift f rec_f a b =
  ruleTrans (axLift f (reify a) (reify b)) (rec_f a)

evalCorrect_Post :
  (f : Fun1) (h : Fun2)
  (rec_h : (j k : Tree) -> EvalCorrect2 h j k)
  (rec_f : (j : Tree) -> EvalCorrect1 f j)
  (a b : Tree) -> EvalCorrect2 (Post f h) a b
evalCorrect_Post f h rec_h rec_f a b =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    eh : Tree
    eh = evalFun2 h a b

    s1 : Deriv (atomic (eqn (ap2 (Post f h) aT bT) (ap1 f (ap2 h aT bT))))
    s1 = axPost f h aT bT

    s2 : Deriv (atomic (eqn (ap1 f (ap2 h aT bT)) (ap1 f (reify eh))))
    s2 = cong1 f (rec_h a b)

    s3 : Deriv (atomic (eqn (ap1 f (reify eh)) (reify (evalFun1 f eh))))
    s3 = rec_f eh
  in ruleTrans s1 (ruleTrans s2 s3)

evalCorrect_Fan :
  (h1 h2 h : Fun2)
  (rec_h1 : (j k : Tree) -> EvalCorrect2 h1 j k)
  (rec_h2 : (j k : Tree) -> EvalCorrect2 h2 j k)
  (rec_h  : (j k : Tree) -> EvalCorrect2 h  j k)
  (a b : Tree) -> EvalCorrect2 (Fan h1 h2 h) a b
evalCorrect_Fan h1 h2 h rec_h1 rec_h2 rec_h a b =
  let
    aT : Term
    aT = reify a

    bT : Term
    bT = reify b

    e1 : Tree
    e1 = evalFun2 h1 a b

    e2 : Tree
    e2 = evalFun2 h2 a b

    s1 : Deriv (atomic (eqn (ap2 (Fan h1 h2 h) aT bT)
                             (ap2 h (ap2 h1 aT bT) (ap2 h2 aT bT))))
    s1 = axFan h1 h2 h aT bT

    s2 : Deriv (atomic (eqn (ap2 h (ap2 h1 aT bT) (ap2 h2 aT bT))
                             (ap2 h (reify e1)    (ap2 h2 aT bT))))
    s2 = congL h (ap2 h2 aT bT) (rec_h1 a b)

    s3 : Deriv (atomic (eqn (ap2 h (reify e1) (ap2 h2 aT bT))
                             (ap2 h (reify e1) (reify e2))))
    s3 = congR h (reify e1) (rec_h2 a b)

    s4 : Deriv (atomic (eqn (ap2 h (reify e1) (reify e2))
                             (reify (evalFun2 h e1 e2))))
    s4 = rec_h e1 e2
  in ruleTrans s1 (ruleTrans s2 (ruleTrans s3 s4))

------------------------------------------------------------------------
-- evalCorrect_RecP : Fun2 analog of eval_correct_RecZ.
--
-- Tree-induction on the second argument b.  Base case (b = lf):
--   axRecPLf s p  gives  ap2 (RecP s) p O = O = reify lf.
-- Step case (b = nd b1 b2): mirror eval_correct_RecZ's recursion,
-- with axRecPNd in place of axRecNd and an explicit p-arg threaded
-- through.

evalCorrect_RecP :
  (s : Fun2)
  (rec_s : (j k : Tree) -> EvalCorrect2 s j k)
  (a b : Tree) -> EvalCorrect2 (RecP s) a b
evalCorrect_RecP s rec_s a lf       = axRecPLf s (reify a)
evalCorrect_RecP s rec_s a (nd b1 b2) =
  let
    aT : Term
    aT = reify a

    b1T : Term
    b1T = reify b1

    b2T : Term
    b2T = reify b2

    rb1T : Term
    rb1T = reify (evalFun2 (RecP s) a b1)

    rb2T : Term
    rb2T = reify (evalFun2 (RecP s) a b2)

    -- Step 1: axRecPNd at p = aT, a = b1T, b = b2T.
    step1 : Deriv (atomic (eqn (ap2 (RecP s) aT (ap2 Pair b1T b2T))
                               (ap2 s (ap2 Pair aT (ap2 Pair b1T b2T))
                                       (ap2 Pair (ap2 (RecP s) aT b1T)
                                                  (ap2 (RecP s) aT b2T)))))
    step1 = axRecPNd s aT b1T b2T

    -- IHs on (a, b1) and (a, b2).
    ih_b1 : Deriv (atomic (eqn (ap2 (RecP s) aT b1T) rb1T))
    ih_b1 = evalCorrect_RecP s rec_s a b1

    ih_b2 : Deriv (atomic (eqn (ap2 (RecP s) aT b2T) rb2T))
    ih_b2 = evalCorrect_RecP s rec_s a b2

    -- Step 2: bridge the inner Pair via the IHs.
    inner_pair_eq : Deriv (atomic (eqn
                      (ap2 Pair (ap2 (RecP s) aT b1T) (ap2 (RecP s) aT b2T))
                      (ap2 Pair rb1T rb2T)))
    inner_pair_eq = ruleTrans (congL Pair (ap2 (RecP s) aT b2T) ih_b1)
                              (congR Pair rb1T ih_b2)

    step2 : Deriv (atomic (eqn
              (ap2 s (ap2 Pair aT (ap2 Pair b1T b2T))
                     (ap2 Pair (ap2 (RecP s) aT b1T) (ap2 (RecP s) aT b2T)))
              (ap2 s (ap2 Pair aT (ap2 Pair b1T b2T))
                     (ap2 Pair rb1T rb2T))))
    step2 = congR s (ap2 Pair aT (ap2 Pair b1T b2T)) inner_pair_eq

    -- Step 3: rec_s at canonical inputs (nd a (nd b1 b2), nd rb1 rb2).
    -- reify (nd a (nd b1 b2)) = ap2 Pair aT (ap2 Pair b1T b2T)
    -- reify (nd (evalFun2 (RecP s) a b1) (evalFun2 (RecP s) a b2)) = ap2 Pair rb1T rb2T
    -- definitionally, so step3's LHS matches step2's RHS.
    step3 : Deriv (atomic (eqn
              (ap2 s (ap2 Pair aT (ap2 Pair b1T b2T))
                     (ap2 Pair rb1T rb2T))
              (reify (evalFun2 s (nd a (nd b1 b2))
                                  (nd (evalFun2 (RecP s) a b1)
                                      (evalFun2 (RecP s) a b2))))))
    step3 = rec_s (nd a (nd b1 b2))
                  (nd (evalFun2 (RecP s) a b1) (evalFun2 (RecP s) a b2))

  in ruleTrans step1 (ruleTrans step2 step3)
