{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.Thm.StepProto
--
-- Session A->B boundary de-risk prototype:  validate the concrete
-- step function used to build  thmT : Fun1  in BRA2.Thm.ThmT.
--
-- Construction:
--   thmTProto  =  Rec O stepProto
--   stepProto  =  Fan discComb branchesTop IfLf
--     discComb     = Lift (Comp Fst Fst)             -- Fst(Fst p1)
--     branchesTop  = Fan dispatch (Post Snd Pair) Pair
--       sndProj    = Post Snd Pair                    -- (a,b) |-> b
--       dispatch   = Fan checkTag1 branch1 IfLf       -- nested cascade
--       checkTagN  = Fan (Lift (KT tagCodeN)) (Lift Fst) TreeEq
--                    -- = TreeEq(tagCodeN, Fst p1)
--       axIBody    = Lift Snd                         -- Snd p1 = payload
--       mpBody     = Post Fst (Post Snd (Post Snd Pair))
--                    -- = Fst(Snd p2)
--
-- Top-level tagged proof:  Fst(Fst p1) = O , so IfLf takes the leaf
-- branch  =  dispatch(p1, p2) , which then case-analyzes the tag.
-- Inner sub-proof pair (when y1 has form  nd (nd _ _) _ ):
--  Fst(Fst p1) = Pair _ _ , so IfLf takes the node branch  =  p2 ,
-- and  Rec  passes the recursion result through unchanged.
--
-- Tags start at  suc zero  so that  natCode tag  is always a
-- non-leaf node (otherwise  Fst(reify (natCode 0)) = Fst O  has no
-- defining axiom).  The real  Tag.agda  must follow this convention.
--
-- All heavy reductions live in one  abstract  block.  Two consumer-
-- visible lemmas:
--   axI_dispatch         (a non-recursive primitive)
--   mp_dispatch_sub (a recursive primitive, takes a sub-proof
--                         derivation as hypothesis)
--
-- Zero postulates, zero holes.

module BRA2.Thm.StepProto where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.Deriv

------------------------------------------------------------------------
-- Prototype tags (start at 1, see header).

tagAxIProto : Nat
tagAxIProto = suc zero

tagMpProto : Nat
tagMpProto = suc (suc zero)

------------------------------------------------------------------------
-- Reified tag codes.  Definitionally:
--   tagCode1 = ap2 Pair O O
--   tagCode2 = ap2 Pair O (ap2 Pair O O)

tagCode1 : Term
tagCode1 = reify (natCode tagAxIProto)

tagCode2 : Term
tagCode2 = reify (natCode tagMpProto)

------------------------------------------------------------------------
-- Encodings.

encAxIProto : Term -> Tree
encAxIProto t = nd (natCode tagAxIProto) (code t)

encMpProto : Tree -> Tree -> Tree
encMpProto y1 y2 = nd (natCode tagMpProto) (nd y1 y2)

------------------------------------------------------------------------
-- Heavy block: combinator construction, reductions, dispatch lemmas.

abstract

  ------------------------------------------------------------------
  -- Step function combinators.

  sndProj : Fun2
  sndProj = Post Snd Pair

  discComb : Fun2
  discComb = Lift (Comp Fst Fst)

  axIBody : Fun2
  axIBody = Lift Snd

  mpBody : Fun2
  mpBody = Post Fst (Post Snd (Post Snd Pair))

  fbBody : Fun2
  fbBody = Lift (KT O)

  checkTag1 : Fun2
  checkTag1 = Fan (Lift (KT tagCode1)) (Lift Fst) TreeEq

  checkTag2 : Fun2
  checkTag2 = Fan (Lift (KT tagCode2)) (Lift Fst) TreeEq

  branch2 : Fun2
  branch2 = Fan mpBody fbBody Pair

  next1 : Fun2
  next1 = Fan checkTag2 branch2 IfLf

  branch1 : Fun2
  branch1 = Fan axIBody next1 Pair

  dispatch : Fun2
  dispatch = Fan checkTag1 branch1 IfLf

  branchesTop : Fun2
  branchesTop = Fan dispatch sndProj Pair

  stepProto : Fun2
  stepProto = Fan discComb branchesTop IfLf

  -- Wrapper to absorb the  Pair O ...  prefix introduced by  Rec  (now
  -- defined as  Comp2 (treeRec Z s) Z I , so axRecNd RHS first arg =
  --   Pair O (input) ).  Equationally:
  --   ap2 stepProtoWrapped (Pair O input) recs
  --     = ap2 stepProto (Snd (Pair O input)) recs = ap2 stepProto input recs
  stepProtoWrapped : Fun2
  stepProtoWrapped = Fan (Lift Snd) (Post Snd Pair) stepProto

  thmTProto : Fun1
  thmTProto = Rec stepProtoWrapped

  -- Bridge: thmTProto (Pair u v) = stepProto (Pair u v) recs
  --   where recs = Pair (thmTProto u) (thmTProto v).
  thmTProtoUnfoldStep : (u v : Term) ->
    Deriv (atomic (eqn (ap1 thmTProto (ap2 Pair u v))
                       (ap2 stepProto (ap2 Pair u v)
                                       (ap2 Pair (ap1 thmTProto u)
                                                 (ap1 thmTProto v)))))
  thmTProtoUnfoldStep u v =
    let a : Term
        a = ap2 Pair u v
        b : Term
        b = ap2 Pair (ap1 thmTProto u) (ap1 thmTProto v)
        aW : Term
        aW = ap2 Pair O a
        e1a : Deriv (atomic (eqn (ap1 thmTProto a) (ap2 stepProtoWrapped aW b)))
        e1a = axRecNd stepProtoWrapped u v
        unfoldFan : Deriv (atomic (eqn (ap2 stepProtoWrapped aW b)
                                       (ap2 stepProto (ap2 (Lift Snd) aW b)
                                                       (ap2 (Post Snd Pair) aW b))))
        unfoldFan = axFan (Lift Snd) (Post Snd Pair) stepProto aW b
        leftRed : Deriv (atomic (eqn (ap2 (Lift Snd) aW b) a))
        leftRed = ruleTrans (axLift Snd aW b) (axSnd O a)
        rightRed : Deriv (atomic (eqn (ap2 (Post Snd Pair) aW b) b))
        rightRed = ruleTrans (axPost Snd Pair aW b) (axSnd aW b)
        congLft = congL stepProto (ap2 (Post Snd Pair) aW b) leftRed
        congRgt = congR stepProto a rightRed
    in ruleTrans e1a (ruleTrans unfoldFan (ruleTrans congLft congRgt))

  ------------------------------------------------------------------
  -- TreeEq reductions on the two concrete tag codes.

  -- TreeEq(tagCode1, tagCode1) = O   where  tagCode1 = Pair O O.
  teqAxIAxI : Deriv (atomic (eqn (ap2 TreeEq tagCode1 tagCode1) O))
  teqAxIAxI =
    let s1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O))
                                 (ap2 IfLf (ap2 TreeEq O O)
                                           (ap2 Pair (ap2 TreeEq O O)
                                                     (ap2 Pair O O)))))
        s1 = axTreeEqNN O O O O
        s2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq O O)
                                          (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))
                                 (ap2 IfLf O
                                          (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))))
        s2 = congL IfLf (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)) axTreeEqLL
        s3 : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O))
                                 (ap2 Pair O (ap2 Pair O O))))
        s3 = congL Pair (ap2 Pair O O) axTreeEqLL
        s4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))
                                 (ap2 IfLf O (ap2 Pair O (ap2 Pair O O)))))
        s4 = congR IfLf O s3
        s5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair O (ap2 Pair O O))) O))
        s5 = axIfLfL O (ap2 Pair O O)
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s4 s5))

  -- TreeEq(tagCode1, tagCode2) = Pair O O    where  tagCode2 = Pair O (Pair O O).
  teqAxIMp : Deriv (atomic (eqn (ap2 TreeEq tagCode1 tagCode2) (ap2 Pair O O)))
  teqAxIMp =
    let s1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O (ap2 Pair O O)))
                                 (ap2 IfLf (ap2 TreeEq O O)
                                           (ap2 Pair (ap2 TreeEq O (ap2 Pair O O))
                                                     (ap2 Pair O O)))))
        s1 = axTreeEqNN O O O (ap2 Pair O O)
        s2 : Deriv (atomic (eqn (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O)))
        s2 = axTreeEqLN O O
        s3 : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O))
                                 (ap2 Pair (ap2 Pair O O) (ap2 Pair O O))))
        s3 = congL Pair (ap2 Pair O O) s2
        s4 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq O O) (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O)))
                                 (ap2 IfLf O                (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O)))))
        s4 = congL IfLf (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O)) axTreeEqLL
        s5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 TreeEq O (ap2 Pair O O)) (ap2 Pair O O)))
                                 (ap2 IfLf O (ap2 Pair (ap2 Pair O O) (ap2 Pair O O)))))
        s5 = congR IfLf O s3
        s6 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 Pair O O) (ap2 Pair O O))) (ap2 Pair O O)))
        s6 = axIfLfL (ap2 Pair O O) (ap2 Pair O O)
    in ruleTrans s1 (ruleTrans s4 (ruleTrans s5 s6))

  -- TreeEq(tagCode2, tagCode2) = O .   tagCode2 = Pair O (Pair O O).
  teqMpMp : Deriv (atomic (eqn (ap2 TreeEq tagCode2 tagCode2) O))
  teqMpMp =
    let -- TE (P O (P O O)) (P O (P O O))
        --   = IfLf (TE O O) (P (TE (P O O) (P O O)) (P O O))
        s1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O (ap2 Pair O O))
                                            (ap2 Pair O (ap2 Pair O O)))
                                 (ap2 IfLf (ap2 TreeEq O O)
                                           (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O))
                                                     (ap2 Pair O O)))))
        s1 = axTreeEqNN O (ap2 Pair O O) O (ap2 Pair O O)
        -- inner: TE (P O O) (P O O)
        --   = IfLf (TE O O) (P (TE O O) (P O O)) = O  (mirrors teq_1_1)
        teq_inner : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) O))
        teq_inner =
          let i1 : Deriv (atomic (eqn (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O))
                                       (ap2 IfLf (ap2 TreeEq O O)
                                                 (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))))
              i1 = axTreeEqNN O O O O
              i2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq O O) (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))
                                       (ap2 IfLf O                (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))))
              i2 = congL IfLf (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)) axTreeEqLL
              i3 : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O))
                                       (ap2 Pair O (ap2 Pair O O))))
              i3 = congL Pair (ap2 Pair O O) axTreeEqLL
              i4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 TreeEq O O) (ap2 Pair O O)))
                                       (ap2 IfLf O (ap2 Pair O (ap2 Pair O O)))))
              i4 = congR IfLf O i3
              i5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair O (ap2 Pair O O))) O))
              i5 = axIfLfL O (ap2 Pair O O)
          in ruleTrans i1 (ruleTrans i2 (ruleTrans i4 i5))
        s2 : Deriv (atomic (eqn (ap2 IfLf (ap2 TreeEq O O)
                                          (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) (ap2 Pair O O)))
                                 (ap2 IfLf O
                                          (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) (ap2 Pair O O)))))
        s2 = congL IfLf (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) (ap2 Pair O O)) axTreeEqLL
        s3 : Deriv (atomic (eqn (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) (ap2 Pair O O))
                                 (ap2 Pair O (ap2 Pair O O))))
        s3 = congL Pair (ap2 Pair O O) teq_inner
        s4 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 TreeEq (ap2 Pair O O) (ap2 Pair O O)) (ap2 Pair O O)))
                                 (ap2 IfLf O (ap2 Pair O (ap2 Pair O O)))))
        s4 = congR IfLf O s3
        s5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair O (ap2 Pair O O))) O))
        s5 = axIfLfL O (ap2 Pair O O)
    in ruleTrans s1 (ruleTrans s2 (ruleTrans s4 s5))

  ------------------------------------------------------------------
  -- Component evaluations on a generic (P1, P2).

  -- ap2 sndProj a b = b   (sndProj = Post Snd Pair).
  sndProj_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 sndProj a b) b))
  sndProj_eval a b =
    let s1 : Deriv (atomic (eqn (ap2 (Post Snd Pair) a b)
                                 (ap1 Snd (ap2 Pair a b))))
        s1 = axPost Snd Pair a b
        s2 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
        s2 = axSnd a b
    in ruleTrans s1 s2

  -- ap2 discComb a b = Fst(Fst a)   (discComb = Lift (Comp Fst Fst)).
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

  -- ap2 axIBody a b = Snd a .
  axIBody_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 axIBody a b) (ap1 Snd a)))
  axIBody_eval a b = axLift Snd a b

  -- ap2 mpBody a b = Fst(Snd b)   (mpBody = Post Fst (Post Snd (Post Snd Pair))).
  mpBody_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 mpBody a b) (ap1 Fst (ap1 Snd b))))
  mpBody_eval a b =
    let s1 : Deriv (atomic (eqn (ap2 (Post Fst (Post Snd (Post Snd Pair))) a b)
                                 (ap1 Fst (ap2 (Post Snd (Post Snd Pair)) a b))))
        s1 = axPost Fst (Post Snd (Post Snd Pair)) a b
        s2 : Deriv (atomic (eqn (ap2 (Post Snd (Post Snd Pair)) a b)
                                 (ap1 Snd (ap2 (Post Snd Pair) a b))))
        s2 = axPost Snd (Post Snd Pair) a b
        s3 : Deriv (atomic (eqn (ap2 (Post Snd Pair) a b)
                                 (ap1 Snd (ap2 Pair a b))))
        s3 = axPost Snd Pair a b
        s4 : Deriv (atomic (eqn (ap1 Snd (ap2 Pair a b)) b))
        s4 = axSnd a b
        -- chain inner: Post Snd Pair (a,b) = b
        s34 : Deriv (atomic (eqn (ap2 (Post Snd Pair) a b) b))
        s34 = ruleTrans s3 s4
        -- chain mid: Post Snd (Post Snd Pair) (a,b) = Snd b
        s5 : Deriv (atomic (eqn (ap1 Snd (ap2 (Post Snd Pair) a b)) (ap1 Snd b)))
        s5 = cong1 Snd s34
        s_mid : Deriv (atomic (eqn (ap2 (Post Snd (Post Snd Pair)) a b) (ap1 Snd b)))
        s_mid = ruleTrans s2 s5
        -- chain outer: Fst(Snd b)
        s6 : Deriv (atomic (eqn (ap1 Fst (ap2 (Post Snd (Post Snd Pair)) a b))
                                 (ap1 Fst (ap1 Snd b))))
        s6 = cong1 Fst s_mid
    in ruleTrans s1 s6

  -- checkTag1 (a, b) = TreeEq(tagCode1, Fst a).
  checkTag1_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 checkTag1 a b) (ap2 TreeEq tagCode1 (ap1 Fst a))))
  checkTag1_eval a b =
    let s1 : Deriv (atomic (eqn (ap2 (Fan (Lift (KT tagCode1)) (Lift Fst) TreeEq) a b)
                                 (ap2 TreeEq (ap2 (Lift (KT tagCode1)) a b) (ap2 (Lift Fst) a b))))
        s1 = axFan (Lift (KT tagCode1)) (Lift Fst) TreeEq a b
        s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode1)) a b) tagCode1))
        s2 = ruleTrans (axLift (KT tagCode1) a b) (axKT (natCode tagAxIProto) a)
        s3 : Deriv (atomic (eqn (ap2 (Lift Fst) a b) (ap1 Fst a)))
        s3 = axLift Fst a b
        s4 : Deriv (atomic (eqn (ap2 TreeEq (ap2 (Lift (KT tagCode1)) a b) (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCode1 (ap2 (Lift Fst) a b))))
        s4 = congL TreeEq (ap2 (Lift Fst) a b) s2
        s5 : Deriv (atomic (eqn (ap2 TreeEq tagCode1 (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCode1 (ap1 Fst a))))
        s5 = congR TreeEq tagCode1 s3
    in ruleTrans s1 (ruleTrans s4 s5)

  checkTag2_eval : (a b : Term) ->
    Deriv (atomic (eqn (ap2 checkTag2 a b) (ap2 TreeEq tagCode2 (ap1 Fst a))))
  checkTag2_eval a b =
    let s1 : Deriv (atomic (eqn (ap2 (Fan (Lift (KT tagCode2)) (Lift Fst) TreeEq) a b)
                                 (ap2 TreeEq (ap2 (Lift (KT tagCode2)) a b) (ap2 (Lift Fst) a b))))
        s1 = axFan (Lift (KT tagCode2)) (Lift Fst) TreeEq a b
        s2 : Deriv (atomic (eqn (ap2 (Lift (KT tagCode2)) a b) tagCode2))
        s2 = ruleTrans (axLift (KT tagCode2) a b) (axKT (natCode tagMpProto) a)
        s3 : Deriv (atomic (eqn (ap2 (Lift Fst) a b) (ap1 Fst a)))
        s3 = axLift Fst a b
        s4 : Deriv (atomic (eqn (ap2 TreeEq (ap2 (Lift (KT tagCode2)) a b) (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCode2 (ap2 (Lift Fst) a b))))
        s4 = congL TreeEq (ap2 (Lift Fst) a b) s2
        s5 : Deriv (atomic (eqn (ap2 TreeEq tagCode2 (ap2 (Lift Fst) a b))
                                 (ap2 TreeEq tagCode2 (ap1 Fst a))))
        s5 = congR TreeEq tagCode2 s3
    in ruleTrans s1 (ruleTrans s4 s5)

  ------------------------------------------------------------------
  -- Top-level step characteristic lemmas.

  -- Inner-pair passthrough:  if  Fst(Fst a) = Pair x y , then
  --  ap2 stepProto a b = b .  Used at the inner sub-proof pair node
  -- (the Snd-child of an mp encoding) to extract the pair of
  -- recursion results.
  stepProto_else : (a b x y : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Fst a)) (ap2 Pair x y))) ->
    Deriv (atomic (eqn (ap2 stepProto a b) b))
  stepProto_else a b x y discPair =
    let -- ap2 stepProto a b = ap2 IfLf (discComb a b) (branchesTop a b)   [axFan]
        e1 : Deriv (atomic (eqn (ap2 stepProto a b)
                                 (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))))
        e1 = axFan discComb branchesTop IfLf a b
        -- discComb a b = Fst(Fst a) = Pair x y
        e2a : Deriv (atomic (eqn (ap2 discComb a b) (ap1 Fst (ap1 Fst a))))
        e2a = discComb_eval a b
        e2 : Deriv (atomic (eqn (ap2 discComb a b) (ap2 Pair x y)))
        e2 = ruleTrans e2a discPair
        -- branchesTop a b = ap2 Pair (dispatch a b) (sndProj a b) = Pair (dispatch a b) b
        e3a : Deriv (atomic (eqn (ap2 branchesTop a b)
                                  (ap2 Pair (ap2 dispatch a b) (ap2 sndProj a b))))
        e3a = axFan dispatch sndProj Pair a b
        e3b : Deriv (atomic (eqn (ap2 sndProj a b) b))
        e3b = sndProj_eval a b
        e3 : Deriv (atomic (eqn (ap2 branchesTop a b)
                                 (ap2 Pair (ap2 dispatch a b) b)))
        e3 = ruleTrans e3a (congR Pair (ap2 dispatch a b) e3b)
        -- substitute into e1: stepProto a b = IfLf (Pair x y) (Pair (dispatch a b) b)
        e4 : Deriv (atomic (eqn (ap2 IfLf (ap2 discComb a b) (ap2 branchesTop a b))
                                 (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))))
        e4 = congL IfLf (ap2 branchesTop a b) e2
        e5 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 branchesTop a b))
                                 (ap2 IfLf (ap2 Pair x y) (ap2 Pair (ap2 dispatch a b) b))))
        e5 = congR IfLf (ap2 Pair x y) e3
        -- IfLf (Pair x y) (Pair A B) = B
        e6 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair x y) (ap2 Pair (ap2 dispatch a b) b)) b))
        e6 = axIfLfN x y (ap2 dispatch a b) b
    in ruleTrans e1 (ruleTrans e4 (ruleTrans e5 e6))

  -- Top-tag passthrough:  if  Fst(Fst a) = O , then
  --  ap2 stepProto a b = ap2 dispatch a b .
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
        e6 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap2 dispatch a b) b)) (ap2 dispatch a b)))
        e6 = axIfLfL (ap2 dispatch a b) b
    in ruleTrans e1 (ruleTrans e4 (ruleTrans e5 e6))

  ------------------------------------------------------------------
  -- Tag-discriminator computation:  Fst(Fst (Pair tagCodeN payload)) = O
  -- since tagCodeN starts with  Pair O ... .

  fstFst_tag1 : (payload : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tagCode1 payload))) O))
  fstFst_tag1 payload =
    let e1 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagCode1 payload)) tagCode1))
        e1 = axFst tagCode1 payload
        e2 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tagCode1 payload)))
                                 (ap1 Fst tagCode1)))
        e2 = cong1 Fst e1
        e3 : Deriv (atomic (eqn (ap1 Fst tagCode1) O))
        e3 = axFst O O
    in ruleTrans e2 e3

  fstFst_tag2 : (payload : Term) ->
    Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tagCode2 payload))) O))
  fstFst_tag2 payload =
    let e1 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair tagCode2 payload)) tagCode2))
        e1 = axFst tagCode2 payload
        e2 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst (ap2 Pair tagCode2 payload)))
                                 (ap1 Fst tagCode2)))
        e2 = cong1 Fst e1
        -- tagCode2 = Pair O (Pair O O), so Fst tagCode2 = O
        e3 : Deriv (atomic (eqn (ap1 Fst tagCode2) O))
        e3 = axFst O (ap2 Pair O O)
    in ruleTrans e2 e3

  ------------------------------------------------------------------
  -- Dispatch reductions at each tag.

  -- dispatch (Pair tagCode1 payload) b = payload .
  dispatch_axI : (payload b : Term) ->
    Deriv (atomic (eqn (ap2 dispatch (ap2 Pair tagCode1 payload) b) payload))
  dispatch_axI payload b =
    let -- dispatch a b = ap2 IfLf (checkTag1 a b) (branch1 a b).
        a : Term
        a = ap2 Pair tagCode1 payload
        e1 : Deriv (atomic (eqn (ap2 dispatch a b)
                                 (ap2 IfLf (ap2 checkTag1 a b) (ap2 branch1 a b))))
        e1 = axFan checkTag1 branch1 IfLf a b
        -- checkTag1 a b = TreeEq(tagCode1, Fst a) = TreeEq(tagCode1, tagCode1) = O
        e2a : Deriv (atomic (eqn (ap2 checkTag1 a b) (ap2 TreeEq tagCode1 (ap1 Fst a))))
        e2a = checkTag1_eval a b
        e2b : Deriv (atomic (eqn (ap1 Fst a) tagCode1))
        e2b = axFst tagCode1 payload
        e2c : Deriv (atomic (eqn (ap2 TreeEq tagCode1 (ap1 Fst a))
                                  (ap2 TreeEq tagCode1 tagCode1)))
        e2c = congR TreeEq tagCode1 e2b
        e2 : Deriv (atomic (eqn (ap2 checkTag1 a b) O))
        e2 = ruleTrans e2a (ruleTrans e2c teqAxIAxI)
        -- branch1 a b = Pair (axIBody a b) (next1 a b) = Pair (Snd a) (next1 a b)
        --   = Pair payload (next1 a b)
        e3a : Deriv (atomic (eqn (ap2 branch1 a b)
                                  (ap2 Pair (ap2 axIBody a b) (ap2 next1 a b))))
        e3a = axFan axIBody next1 Pair a b
        e3b : Deriv (atomic (eqn (ap2 axIBody a b) (ap1 Snd a)))
        e3b = axIBody_eval a b
        e3c : Deriv (atomic (eqn (ap1 Snd a) payload))
        e3c = axSnd tagCode1 payload
        e3d : Deriv (atomic (eqn (ap2 axIBody a b) payload))
        e3d = ruleTrans e3b e3c
        e3 : Deriv (atomic (eqn (ap2 branch1 a b)
                                 (ap2 Pair payload (ap2 next1 a b))))
        e3 = ruleTrans e3a (congL Pair (ap2 next1 a b) e3d)
        -- IfLf O (Pair payload (next1 a b)) = payload
        e4 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkTag1 a b) (ap2 branch1 a b))
                                 (ap2 IfLf O                  (ap2 branch1 a b))))
        e4 = congL IfLf (ap2 branch1 a b) e2
        e5 : Deriv (atomic (eqn (ap2 IfLf O (ap2 branch1 a b))
                                 (ap2 IfLf O (ap2 Pair payload (ap2 next1 a b)))))
        e5 = congR IfLf O e3
        e6 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair payload (ap2 next1 a b))) payload))
        e6 = axIfLfL payload (ap2 next1 a b)
    in ruleTrans e1 (ruleTrans e4 (ruleTrans e5 e6))

  -- dispatch (Pair tagCode2 payload) b = mpBody result = Fst(Snd b) .
  dispatch_mp : (payload b : Term) ->
    Deriv (atomic (eqn (ap2 dispatch (ap2 Pair tagCode2 payload) b)
                       (ap1 Fst (ap1 Snd b))))
  dispatch_mp payload b =
    let a : Term
        a = ap2 Pair tagCode2 payload
        -- Outer: dispatch a b = IfLf (checkTag1 a b) (branch1 a b).
        e1 : Deriv (atomic (eqn (ap2 dispatch a b)
                                 (ap2 IfLf (ap2 checkTag1 a b) (ap2 branch1 a b))))
        e1 = axFan checkTag1 branch1 IfLf a b
        -- checkTag1 a b = TreeEq(tagCode1, Fst a) = TreeEq(tagCode1, tagCode2) = Pair O O.
        c1a : Deriv (atomic (eqn (ap2 checkTag1 a b) (ap2 TreeEq tagCode1 (ap1 Fst a))))
        c1a = checkTag1_eval a b
        c1b : Deriv (atomic (eqn (ap1 Fst a) tagCode2))
        c1b = axFst tagCode2 payload
        c1c : Deriv (atomic (eqn (ap2 TreeEq tagCode1 (ap1 Fst a))
                                  (ap2 TreeEq tagCode1 tagCode2)))
        c1c = congR TreeEq tagCode1 c1b
        check1_eq : Deriv (atomic (eqn (ap2 checkTag1 a b) (ap2 Pair O O)))
        check1_eq = ruleTrans c1a (ruleTrans c1c teqAxIMp)
        -- branch1 a b = Pair (axIBody a b) (next1 a b)
        b1a : Deriv (atomic (eqn (ap2 branch1 a b)
                                  (ap2 Pair (ap2 axIBody a b) (ap2 next1 a b))))
        b1a = axFan axIBody next1 Pair a b
        -- IfLf (Pair O O) (branch1 a b) = next1 a b
        e_outer : Deriv (atomic (eqn (ap2 IfLf (ap2 checkTag1 a b) (ap2 branch1 a b))
                                      (ap2 IfLf (ap2 Pair O O)    (ap2 branch1 a b))))
        e_outer = congL IfLf (ap2 branch1 a b) check1_eq
        e_outer2 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair O O) (ap2 branch1 a b))
                                       (ap2 IfLf (ap2 Pair O O)
                                                  (ap2 Pair (ap2 axIBody a b) (ap2 next1 a b)))))
        e_outer2 = congR IfLf (ap2 Pair O O) b1a
        e_outer3 : Deriv (atomic (eqn (ap2 IfLf (ap2 Pair O O)
                                                 (ap2 Pair (ap2 axIBody a b) (ap2 next1 a b)))
                                       (ap2 next1 a b)))
        e_outer3 = axIfLfN O O (ap2 axIBody a b) (ap2 next1 a b)
        -- chain: dispatch a b = next1 a b
        e_disp_to_next1 : Deriv (atomic (eqn (ap2 dispatch a b) (ap2 next1 a b)))
        e_disp_to_next1 = ruleTrans e1 (ruleTrans e_outer (ruleTrans e_outer2 e_outer3))
        -- next1 a b = IfLf (checkTag2 a b) (branch2 a b).
        n1 : Deriv (atomic (eqn (ap2 next1 a b)
                                 (ap2 IfLf (ap2 checkTag2 a b) (ap2 branch2 a b))))
        n1 = axFan checkTag2 branch2 IfLf a b
        -- checkTag2 a b = TreeEq(tagCode2, Fst a) = TreeEq(tagCode2, tagCode2) = O.
        c2a : Deriv (atomic (eqn (ap2 checkTag2 a b) (ap2 TreeEq tagCode2 (ap1 Fst a))))
        c2a = checkTag2_eval a b
        c2c : Deriv (atomic (eqn (ap2 TreeEq tagCode2 (ap1 Fst a))
                                  (ap2 TreeEq tagCode2 tagCode2)))
        c2c = congR TreeEq tagCode2 c1b
        check2_eq : Deriv (atomic (eqn (ap2 checkTag2 a b) O))
        check2_eq = ruleTrans c2a (ruleTrans c2c teqMpMp)
        -- branch2 a b = Pair (mpBody a b) (fbBody a b) = Pair (Fst (Snd b)) (fbBody a b)
        b2a : Deriv (atomic (eqn (ap2 branch2 a b)
                                  (ap2 Pair (ap2 mpBody a b) (ap2 fbBody a b))))
        b2a = axFan mpBody fbBody Pair a b
        b2b : Deriv (atomic (eqn (ap2 mpBody a b) (ap1 Fst (ap1 Snd b))))
        b2b = mpBody_eval a b
        b2c : Deriv (atomic (eqn (ap2 branch2 a b)
                                  (ap2 Pair (ap1 Fst (ap1 Snd b)) (ap2 fbBody a b))))
        b2c = ruleTrans b2a (congL Pair (ap2 fbBody a b) b2b)
        -- next1 step: IfLf O (branch2 a b) = mpBody result
        n_step1 : Deriv (atomic (eqn (ap2 IfLf (ap2 checkTag2 a b) (ap2 branch2 a b))
                                      (ap2 IfLf O                   (ap2 branch2 a b))))
        n_step1 = congL IfLf (ap2 branch2 a b) check2_eq
        n_step2 : Deriv (atomic (eqn (ap2 IfLf O (ap2 branch2 a b))
                                      (ap2 IfLf O (ap2 Pair (ap1 Fst (ap1 Snd b))
                                                              (ap2 fbBody a b)))))
        n_step2 = congR IfLf O b2c
        n_step3 : Deriv (atomic (eqn (ap2 IfLf O (ap2 Pair (ap1 Fst (ap1 Snd b))
                                                              (ap2 fbBody a b)))
                                      (ap1 Fst (ap1 Snd b))))
        n_step3 = axIfLfL (ap1 Fst (ap1 Snd b)) (ap2 fbBody a b)
        e_next1_to_fst_snd : Deriv (atomic (eqn (ap2 next1 a b) (ap1 Fst (ap1 Snd b))))
        e_next1_to_fst_snd = ruleTrans n1 (ruleTrans n_step1 (ruleTrans n_step2 n_step3))
    in ruleTrans e_disp_to_next1 e_next1_to_fst_snd

  ------------------------------------------------------------------
  -- Top-level stepProto reductions at each tag (combine
  -- stepProto_top with dispatch_*).

  stepProto_axI : (payload b : Term) ->
    Deriv (atomic (eqn (ap2 stepProto (ap2 Pair tagCode1 payload) b) payload))
  stepProto_axI payload b =
    let a : Term
        a = ap2 Pair tagCode1 payload
        s1 : Deriv (atomic (eqn (ap2 stepProto a b) (ap2 dispatch a b)))
        s1 = stepProto_top a b (fstFst_tag1 payload)
        s2 : Deriv (atomic (eqn (ap2 dispatch a b) payload))
        s2 = dispatch_axI payload b
    in ruleTrans s1 s2

  stepProto_mp : (payload b : Term) ->
    Deriv (atomic (eqn (ap2 stepProto (ap2 Pair tagCode2 payload) b)
                       (ap1 Fst (ap1 Snd b))))
  stepProto_mp payload b =
    let a : Term
        a = ap2 Pair tagCode2 payload
        s1 : Deriv (atomic (eqn (ap2 stepProto a b) (ap2 dispatch a b)))
        s1 = stepProto_top a b (fstFst_tag2 payload)
        s2 : Deriv (atomic (eqn (ap2 dispatch a b) (ap1 Fst (ap1 Snd b))))
        s2 = dispatch_mp payload b
    in ruleTrans s1 s2

  ------------------------------------------------------------------
  -- Inner-pair passthrough at the level of Rec:
  --   ap1 thmTProto (reify (nd (nd (nd y1aL y1aR) y1ar) y1b))
  -- expanded by axRecNd plus stepProto_else gives
  --   Pair (ap1 thmTProto (reify (nd (nd y1aL y1aR) y1ar)))
  --        (ap1 thmTProto (reify y1b)) .
  -- We instantiate this at the specific shape needed for mp: the
  -- inner pair is  (reify y1, reify y2)  where  y1 = nd (nd y1aL y1aR) y1ar .

  inner_pair_passthrough :
    (y1aL y1aR y1ar y2 : Tree) ->
    Deriv (atomic (eqn
      (ap1 thmTProto (reify (nd (nd (nd y1aL y1aR) y1ar) y2)))
      (ap2 Pair (ap1 thmTProto (reify (nd (nd y1aL y1aR) y1ar)))
                (ap1 thmTProto (reify y2)))))
  inner_pair_passthrough y1aL y1aR y1ar y2 =
    let y1T : Term
        y1T = reify (nd (nd y1aL y1aR) y1ar)
        y2T : Term
        y2T = reify y2
        -- y1T = ap2 Pair (ap2 Pair (reify y1aL) (reify y1aR)) (reify y1ar)  definitionally.
        P1 : Term
        P1 = ap2 Pair y1T y2T
        P2 : Term
        P2 = ap2 Pair (ap1 thmTProto y1T) (ap1 thmTProto y2T)
        -- axRecNd: ap1 (Rec O stepProto) (Pair y1T y2T) = stepProto P1 P2.
        e1 : Deriv (atomic (eqn (ap1 thmTProto (ap2 Pair y1T y2T)) (ap2 stepProto P1 P2)))
        e1 = thmTProtoUnfoldStep y1T y2T
        -- Fst(Fst P1) = Fst(y1T) = Pair (reify y1aL) (reify y1aR)
        --   y1T = Pair (Pair (reify y1aL) (reify y1aR)) (reify y1ar)
        --   so Fst(y1T) = Pair (reify y1aL) (reify y1aR)
        --   and Fst(Fst P1) = Fst(y1T)
        d1 : Deriv (atomic (eqn (ap1 Fst P1) y1T))
        d1 = axFst y1T y2T
        d2 : Deriv (atomic (eqn (ap1 Fst y1T)
                                 (ap2 Pair (reify y1aL) (reify y1aR))))
        d2 = axFst (ap2 Pair (reify y1aL) (reify y1aR)) (reify y1ar)
        d3 : Deriv (atomic (eqn (ap1 Fst (ap1 Fst P1)) (ap1 Fst y1T)))
        d3 = cong1 Fst d1
        discPair : Deriv (atomic (eqn (ap1 Fst (ap1 Fst P1))
                                       (ap2 Pair (reify y1aL) (reify y1aR))))
        discPair = ruleTrans d3 d2
        -- stepProto_else: stepProto P1 P2 = P2.
        e2 : Deriv (atomic (eqn (ap2 stepProto P1 P2) P2))
        e2 = stepProto_else P1 P2 (reify y1aL) (reify y1aR) discPair
    in ruleTrans e1 e2

  ------------------------------------------------------------------
  -- Consumer-visible dispatch lemmas.

  -- Non-recursive (axI-like) dispatch.
  axI_dispatch : (t : Term) ->
    Deriv (atomic (eqn (ap1 thmTProto (reify (encAxIProto t))) (reify (code t))))
  axI_dispatch t =
    let pT : Term
        pT = reify (code t)
        -- reify (encAxIProto t) = Pair tagCode1 pT  definitionally.
        -- ap1 thmTProto (Pair tagCode1 pT) = stepProto (Pair tagCode1 pT) (Pair (thmT tagCode1) (thmT pT))
        e1 : Deriv (atomic (eqn (ap1 thmTProto (ap2 Pair tagCode1 pT))
                                 (ap2 stepProto (ap2 Pair tagCode1 pT)
                                                (ap2 Pair (ap1 thmTProto tagCode1)
                                                          (ap1 thmTProto pT)))))
        e1 = thmTProtoUnfoldStep tagCode1 pT
        e2 : Deriv (atomic (eqn (ap2 stepProto (ap2 Pair tagCode1 pT)
                                                 (ap2 Pair (ap1 thmTProto tagCode1)
                                                           (ap1 thmTProto pT))) pT))
        e2 = stepProto_axI pT
                (ap2 Pair (ap1 thmTProto tagCode1) (ap1 thmTProto pT))
    in ruleTrans e1 e2

  -- Recursive (mp-like) dispatch with one sub-proof hypothesis.
  --
  -- In production,  y1 = encode (P imp Q) h1  always has shape
  --  nd (natCode tagX) payloadX  with  natCode tagX = nd lf ... ,
  -- so  y1 = nd (nd y1aL y1aR) y1ar  with y1aL = lf, y1aR =
  -- natCode (tagX - 1).  We pattern-match on this prototype shape;
  -- the dispatch lemma in production  ThmT.agda  will receive the
  -- same structure from  encode 's recursion.

  mp_dispatch_sub :
    (y1aL y1aR y1ar y2 : Tree) (Q1 : Term) ->
    Deriv (atomic (eqn (ap1 thmTProto (reify (nd (nd y1aL y1aR) y1ar))) Q1)) ->
    Deriv (atomic (eqn (ap1 thmTProto
                              (reify (encMpProto (nd (nd y1aL y1aR) y1ar) y2))) Q1))
  mp_dispatch_sub y1aL y1aR y1ar y2 Q1 d1 =
    let y1 : Tree
        y1 = nd (nd y1aL y1aR) y1ar
        y1T : Term
        y1T = reify y1
        y2T : Term
        y2T = reify y2
        payT : Term
        payT = ap2 Pair y1T y2T   -- = reify (nd y1 y2)  definitionally
        -- ap1 thmTProto (Pair tagCode2 payT) = stepProto (Pair tagCode2 payT) (Pair (thmT tagCode2) (thmT payT))
        e1 : Deriv (atomic (eqn (ap1 thmTProto (ap2 Pair tagCode2 payT))
                                 (ap2 stepProto (ap2 Pair tagCode2 payT)
                                                 (ap2 Pair (ap1 thmTProto tagCode2)
                                                           (ap1 thmTProto payT)))))
        e1 = thmTProtoUnfoldStep tagCode2 payT
        -- stepProto (Pair tagCode2 payT) (Pair _ thmT_payT) = Fst (Snd (Pair _ thmT_payT)) = Fst thmT_payT
        e2 : Deriv (atomic (eqn (ap2 stepProto (ap2 Pair tagCode2 payT)
                                                  (ap2 Pair (ap1 thmTProto tagCode2)
                                                            (ap1 thmTProto payT)))
                                 (ap1 Fst
                                       (ap1 Snd
                                            (ap2 Pair (ap1 thmTProto tagCode2)
                                                      (ap1 thmTProto payT))))))
        e2 = stepProto_mp payT (ap2 Pair (ap1 thmTProto tagCode2)
                                          (ap1 thmTProto payT))
        -- Snd (Pair x y) = y .
        e3a : Deriv (atomic (eqn (ap1 Snd (ap2 Pair (ap1 thmTProto tagCode2)
                                                     (ap1 thmTProto payT)))
                                  (ap1 thmTProto payT)))
        e3a = axSnd (ap1 thmTProto tagCode2) (ap1 thmTProto payT)
        e3 : Deriv (atomic (eqn (ap1 Fst
                                       (ap1 Snd
                                            (ap2 Pair (ap1 thmTProto tagCode2)
                                                      (ap1 thmTProto payT))))
                                 (ap1 Fst (ap1 thmTProto payT))))
        e3 = cong1 Fst e3a
        -- Inner-pair passthrough:  ap1 thmTProto payT = Pair (thmT y1T) (thmT y2T) .
        e4 : Deriv (atomic (eqn (ap1 thmTProto payT)
                                 (ap2 Pair (ap1 thmTProto y1T) (ap1 thmTProto y2T))))
        e4 = inner_pair_passthrough y1aL y1aR y1ar y2
        e5 : Deriv (atomic (eqn (ap1 Fst (ap1 thmTProto payT))
                                 (ap1 Fst (ap2 Pair (ap1 thmTProto y1T) (ap1 thmTProto y2T)))))
        e5 = cong1 Fst e4
        -- Fst (Pair (thmT y1T) (thmT y2T)) = thmT y1T .
        e6 : Deriv (atomic (eqn (ap1 Fst (ap2 Pair (ap1 thmTProto y1T) (ap1 thmTProto y2T)))
                                 (ap1 thmTProto y1T)))
        e6 = axFst (ap1 thmTProto y1T) (ap1 thmTProto y2T)
        -- chain through to thmT y1T, then use d1 to reach Q1.
    in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 (ruleTrans e5 (ruleTrans e6 d1))))
