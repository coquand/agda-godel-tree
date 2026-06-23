{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BinTreeInd -- the leaf/node binary-tree structural INDUCTION principle
-- for pi-form (explicitly-built) codes, the payoff of route 1.
--
-- Two things are delivered, both GREEN, with NO surjective pairing:
--
--  (1) STRICT CHILD-DESCENT for the pi-tagged node code, keystone-free:
--        descL : leq (s l) (binNode n l r)
--        descR : leq (s r) (binNode n l r)
--      Proof: binNode n l r = pi (s (s O)) payload (payload = pi n (pi l r))
--      is a SUCCESSOR (pi_at_succ), so binNode = s P_outer with
--      P_outer = pi_succ_outer (s O) payload = pred(binNode).  Each child is
--      <= payload (leq_a_pi_a_b / leq_b_pi_a_b) and payload <= P_outer
--      (leq_sigma_right), so child <= P_outer, hence s child <= s P_outer =
--      binNode (T78 s-monotonicity + the pi_at_succ equation).  This is the
--      child-descent obligation that T4.TreeCovInd.covFuel pushes to the
--      client -- discharged here for built nodes with no eta law.
--
--  (2) The covFuel NODE STEP realised through the strong IH (this is "tree
--      induction derived from course-of-values induction"):
--        nodeStep : (covFuel strong IH at  binNode n l r ) -> Q (binNode n l r)
--      i.e. covFuel's IH `(e) -> leq (s e) d -> Q e`, instantiated at the two
--      children via descL/descR and combined by the qnode combinator, yields
--      Q at the node.  So course-of-values DOES give the node case of tree
--      recursion, keystone-free, for pi-form codes.
--
--  (3) The usable leaf/node induction principle  binTreeInd  over the BinM
--      shadow (structural recursion on BinM; the meta structure supplies the
--      leaf/node DISPATCH that an opaque code cannot without surjective
--      pairing).  Its node case is exactly  nodeStep 's content with the IH
--      supplied by the recursion.
--
-- HONEST SCOPE: a FULLY covFuel-routed `binTreeInd` over opaque codes is NOT
-- possible without surjective pairing -- not because of the child-descent
-- (that is (1), keystone-free) but because the covFuel step is universal over
-- d and must DISPATCH leaf-vs-node on an opaque tag, which needs
-- Pair (Fst d)(Snd d) = d.  For codes carried with their BinM shadow the
-- dispatch is free, so binTreeInd + descL/descR/nodeStep give genuine,
-- keystone-free internal binary-tree induction for built trees.
--
-- No holes, no postulates; --safe --without-K --exact-split.

module T4.BinTreeInd where

open import T4.Base

open import T4.BinTree   using ( binLeaf ; binNode ; BinM ; leafM ; nodeM ; codeB )
open import T4.PiPositivity using ( pi_succ_outer ; pi_at_succ )
open import T4.LeqMono   using ( leq_trans ; leq_sigma_right )

open import BRA3.Church      using ( pi ; sigma ; tau ; sub )
open import BRA3.ChurchLeq   using ( leq )
open import BRA3.ChurchT78   using ( T78 )
open import BRA3.TreeDescent using ( leq_a_pi_a_b ; leq_b_pi_a_b )
open import BRA3.RuleInst2   using ( ruleInst2 )

------------------------------------------------------------------------
-- SECTION 1.  Strict child-descent for the pi-tagged node code.

-- Shared: from  leq child payload  derive  leq (s child) (binNode n l r) .
-- (payload = pi n (pi l r) ;  binNode n l r = pi (s (s O)) payload .)
descFromChildLePayload : (n l r child : Term) ->
  Deriv (leq child (ap2 pi n (ap2 pi l r))) ->
  Deriv (leq (ap1 s child) (binNode n l r))
descFromChildLePayload n l r child child_le_payload =
  let payload : Term
      payload = ap2 pi n (ap2 pi l r)
      P_outer : Term
      P_outer = pi_succ_outer (ap1 s O) payload

      -- payload <= P_outer = pred(binNode) , via leq_sigma_right.
      payload_le_Pouter : Deriv (leq payload P_outer)
      payload_le_Pouter =
        leq_sigma_right
          (ap2 sigma (ap2 sigma (ap1 s O) payload)
                     (ap1 tau (ap2 sigma (ap1 s O) payload)))
          payload

      child_le_Pouter : Deriv (leq child P_outer)
      child_le_Pouter = leq_trans child payload P_outer child_le_payload payload_le_Pouter

      -- s-monotonicity:  child <= P_outer  =>  s child <= s P_outer .
      T78_at : Deriv (imp (leq child P_outer)
                          (leq (ap1 s child) (ap1 s P_outer)))
      T78_at = ruleInst2 zero child (suc zero) P_outer refl T78
      sChild_le_sPouter : Deriv (leq (ap1 s child) (ap1 s P_outer))
      sChild_le_sPouter = mp T78_at child_le_Pouter

      -- binNode = pi (s (s O)) payload = s P_outer  (pi_at_succ),
      -- so rewrite the bound  s P_outer -> binNode  inside  sub .
      node_eq : Deriv (eqF (ap2 pi (ap1 s (ap1 s O)) payload) (ap1 s P_outer))
      node_eq = pi_at_succ (ap1 s O) payload
      sub_eq : Deriv (eqF (ap2 sub (ap1 s child) (binNode n l r))
                          (ap2 sub (ap1 s child) (ap1 s P_outer)))
      sub_eq = congR sub (ap1 s child) node_eq
  in ruleTrans sub_eq sChild_le_sPouter

descL : (n l r : Term) -> Deriv (leq (ap1 s l) (binNode n l r))
descL n l r =
  descFromChildLePayload n l r l
    (leq_trans l (ap2 pi l r) (ap2 pi n (ap2 pi l r))
       (leq_a_pi_a_b l r)
       (leq_b_pi_a_b n (ap2 pi l r)))

descR : (n l r : Term) -> Deriv (leq (ap1 s r) (binNode n l r))
descR n l r =
  descFromChildLePayload n l r r
    (leq_trans r (ap2 pi l r) (ap2 pi n (ap2 pi l r))
       (leq_b_pi_a_b l r)
       (leq_b_pi_a_b n (ap2 pi l r)))

------------------------------------------------------------------------
-- SECTION 2.  The covFuel node step: course-of-values strong IH -> node case.
--
-- This is "tree induction derived from course-of-values induction": given the
-- strong IH that covFuel hands the step at a node code d = binNode n l r
-- (Q at every  e < d ), the two children l, r are  < d  by descL/descR, so the
-- IH delivers  Q l  and  Q r , and the qnode combinator yields  Q d .
-- Keystone-free; the only thing NOT covered here is dispatching an opaque d to
-- KNOW it is a node (that needs surjective pairing).

nodeStep :
  (Q : Term -> Formula) ->
  ( (nn l r : Term) -> Deriv (Q l) -> Deriv (Q r) -> Deriv (Q (binNode nn l r)) ) ->
  (n l r : Term) ->
  ( (e : Term) -> Deriv (leq (ap1 s e) (binNode n l r)) -> Deriv (Q e) ) ->
  Deriv (Q (binNode n l r))
nodeStep Q qnode n l r ih =
  qnode n l r (ih l (descL n l r)) (ih r (descR n l r))

------------------------------------------------------------------------
-- SECTION 3.  The usable leaf/node binary-tree induction principle.
--
-- Structural recursion on the BinM shadow supplies the leaf/node dispatch;
-- the node case is nodeStep's content with the IH given by the recursion.

binTreeInd :
  (Q : Term -> Formula) ->
  ( (n : Term) -> Deriv (Q (binLeaf n)) ) ->
  ( (n l r : Term) -> Deriv (Q l) -> Deriv (Q r) -> Deriv (Q (binNode n l r)) ) ->
  (b : BinM) -> Deriv (Q (codeB b))
binTreeInd Q qleaf qnode (leafM n)     = qleaf n
binTreeInd Q qleaf qnode (nodeM n l r) =
  qnode n (codeB l) (codeB r)
    (binTreeInd Q qleaf qnode l)
    (binTreeInd Q qleaf qnode r)
