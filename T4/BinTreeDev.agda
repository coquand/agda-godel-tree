{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BinTreeDev -- (2) of attempt3 §14: a TREE-BUILDING structural function
-- defined by PRIMITIVE RECURSION on the binary-tree recursor  binRec , whose
-- PRESERVATION lemmas collapse to ONE structural induction.  This is the
-- shape of  devF / devCertF / triF  (each maps a tree code to a tree code),
-- so it shows the §14 fix: "the cert is a wf binary tree; tri is structural
-- recursion; preservation is the induction principle."
--
-- The example function is  mirrorFW : Fun1 , which swaps the two children of
-- every node (a non-trivial tree -> tree map):
--
--     mirrorFW (binLeaf n)     = binLeaf n
--     mirrorFW (binNode n l r) = binNode n (mirrorFW r) (mirrorFW l)
--
-- Both defining equations are proved as  Deriv  via the  NP  engine
-- (T4.ParsObj), using the BOTH-children recovery from T4.BinTree.
--
-- Then two PRESERVATION lemmas, each ONE meta induction on  BinM  chaining
-- the defining equations (this is the payoff -- cf. the OPAQUE-cert stall the
-- old triF preservation hit; here the structure is carried by BinM):
--
--     mirrorW_wf    : (b : BinM) -> wf (mirrorFW (codeB b)) = O
--                    -- mirroring PRESERVES well-formedness (isCert-style).
--     mirrorW_invol : (b : BinM) -> mirrorFW (mirrorFW (codeB b)) = codeB b
--                    -- mirroring is an INVOLUTION (a round-trip law).
--
-- No holes, no postulates, no termination warnings.

module T4.BinTreeDev where

open import T4.Base

open import T4.BinTree   using ( binLeaf ; binNode ; binRec ; nIdx ; lIdx ; rIdx
                               ; BinM ; leafM ; nodeM ; codeB )
open import T4.BinTreeWf using ( wf ; wf_leaf ; wf_node )
open import T4.FoldRec   using ( lookupAt )
open import T4.ParsObj   using ( foldOf ; test1 ; module NP )
open import T4.LenR      using ( get_rc )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.ParEnds   using ( pi_O_O )

open import BRA3.Church        using ( pi )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.PairAlgebra   using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Congruence of the  binNode  constructor in its two children.

binNode_cong : (n A A2 B B2 : Term) ->
  Deriv (eqF A A2) -> Deriv (eqF B B2) ->
  Deriv (eqF (binNode n A B) (binNode n A2 B2))
binNode_cong n A A2 B B2 eA eB =
  let inner_eq : Deriv (eqF (ap2 Pair A B) (ap2 Pair A2 B2))
      inner_eq = ruleTrans (congL Pair B eA) (congR Pair A2 eB)
      mid_eq : Deriv (eqF (ap2 Pair n (ap2 Pair A B)) (ap2 Pair n (ap2 Pair A2 B2)))
      mid_eq = congR Pair n inner_eq
  in congR Pair (natCode 2) mid_eq

------------------------------------------------------------------------
-- SECTION 1.  mirrorFW as a  binRec  instance.

cellLeafMir : Fun1
cellLeafMir = C pi (constN 1) get_rc                  -- leaf n -> binLeaf n

cellNodeMir : Fun1                                    -- node n l r -> binNode n (mir r)(mir l)
cellNodeMir = C pi (constN 2) (C pi nIdx (C pi (lookupAt rIdx) (lookupAt lIdx)))

mirrorFW : Fun1
mirrorFW = binRec Z cellLeafMir cellNodeMir

------------------------------------------------------------------------
-- SECTION 2.  mirrorW_leaf :  mirrorFW (binLeaf n) = binLeaf n .

mirrorW_leaf : (n : Term) -> Deriv (eqF (ap1 mirrorFW (binLeaf n)) (binLeaf n))
mirrorW_leaf n =
  let open NP Z cellLeafMir cellNodeMir O n
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
      cellLeafMir_val : Deriv (eqF (ap1 cellLeafMir input_pkg) (binLeaf n))
      cellLeafMir_val =
        ruleTrans (ax_C pi (constN 1) get_rc input_pkg)
          (ruleTrans (congL pi (ap1 get_rc input_pkg) (constN_eq 1 input_pkg))
                     (congR pi (natCode 1) np_rc))
  in ruleTrans (collapse_fst t1_fire) cellLeafMir_val

------------------------------------------------------------------------
-- SECTION 3.  mirrorW_node :  mirrorFW (binNode n l r) = binNode n (mir r)(mir l) .

mirrorW_node : (n l r : Term) ->
  Deriv (eqF (ap1 mirrorFW (binNode n l r))
             (binNode n (ap1 mirrorFW r) (ap1 mirrorFW l)))
mirrorW_node n l r =
  let open NP Z cellLeafMir cellNodeMir (natCode 1) (ap2 Pair n (ap2 Pair l r))

      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair l r))
      sndArg_eq =
        ruleTrans (compose1U_eq Snd get_rc input_pkg)
          (ruleTrans (cong1 Snd np_rc) (axSnd n (ap2 Pair l r)))
      nIdx_eq : Deriv (eqF (ap1 nIdx input_pkg) n)
      nIdx_eq =
        ruleTrans (compose1U_eq Fst get_rc input_pkg)
          (ruleTrans (cong1 Fst np_rc) (axFst n (ap2 Pair l r)))
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) l)
      lIdx_eq =
        ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
          (ruleTrans (cong1 Fst sndArg_eq) (axFst l r))
      rIdx_eq : Deriv (eqF (ap1 rIdx input_pkg) r)
      rIdx_eq =
        ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
          (ruleTrans (cong1 Snd sndArg_eq) (axSnd l r))
      leq_lr_P : Deriv (leq (ap2 Pair l r) P_outer)
      leq_lr_P = leq_trans (ap2 Pair l r) (ap2 Pair n (ap2 Pair l r)) P_outer
                   (leq_pi_right n (ap2 Pair l r)) leq_b_P
      leq_l_P : Deriv (leq l P_outer)
      leq_l_P = leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P
      leq_r_P : Deriv (leq r P_outer)
      leq_r_P = leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P

      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 mirrorFW l))
      recL = np_lookup_gen lIdx l lIdx_eq leq_l_P
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 mirrorFW r))
      recR = np_lookup_gen rIdx r rIdx_eq leq_r_P

      -- inner2 = C pi (lookupAt rIdx)(lookupAt lIdx) -> Pair (mir r)(mir l)  (SWAP).
      inner2_val :
        Deriv (eqF (ap1 (C pi (lookupAt rIdx) (lookupAt lIdx)) input_pkg)
                   (ap2 Pair (ap1 mirrorFW r) (ap1 mirrorFW l)))
      inner2_val =
        ruleTrans (ax_C pi (lookupAt rIdx) (lookupAt lIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt lIdx) input_pkg) recR)
                     (congR pi (ap1 mirrorFW r) recL))
      -- inner1 = C pi nIdx inner2 -> Pair n (Pair (mir r)(mir l)).
      inner1_val :
        Deriv (eqF (ap1 (C pi nIdx (C pi (lookupAt rIdx) (lookupAt lIdx))) input_pkg)
                   (ap2 Pair n (ap2 Pair (ap1 mirrorFW r) (ap1 mirrorFW l))))
      inner1_val =
        ruleTrans (ax_C pi nIdx (C pi (lookupAt rIdx) (lookupAt lIdx)) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi (lookupAt rIdx) (lookupAt lIdx)) input_pkg) nIdx_eq)
                     (congR pi n inner2_val))
      cellNodeMir_val :
        Deriv (eqF (ap1 cellNodeMir input_pkg)
                   (binNode n (ap1 mirrorFW r) (ap1 mirrorFW l)))
      cellNodeMir_val =
        ruleTrans (ax_C pi (constN 2)
                    (C pi nIdx (C pi (lookupAt rIdx) (lookupAt lIdx))) input_pkg)
          (ruleTrans (congL pi (ap1 (C pi nIdx (C pi (lookupAt rIdx) (lookupAt lIdx))) input_pkg)
                          (constN_eq 2 input_pkg))
                     (congR pi (natCode 2) inner1_val))
  in ruleTrans (collapse_snd t1_O) cellNodeMir_val

------------------------------------------------------------------------
-- SECTION 4.  PRESERVATION 1: mirroring preserves well-formedness.
-- ONE meta induction on  BinM  (= the structural induction principle).

mirrorW_wf : (b : BinM) -> Deriv (eqF (ap1 wf (ap1 mirrorFW (codeB b))) O)
mirrorW_wf (leafM n) =
  ruleTrans (cong1 wf (mirrorW_leaf n)) (wf_leaf n)
mirrorW_wf (nodeM n l r) =
  ruleTrans (cong1 wf (mirrorW_node n (codeB l) (codeB r)))
    (ruleTrans (wf_node n (ap1 mirrorFW (codeB r)) (ap1 mirrorFW (codeB l)))
      (ruleTrans (congL pi (ap1 wf (ap1 mirrorFW (codeB l))) (mirrorW_wf r))
        (ruleTrans (congR pi O (mirrorW_wf l)) pi_O_O)))

------------------------------------------------------------------------
-- SECTION 5.  PRESERVATION 2: mirroring is an involution.
-- ONE meta induction on  BinM , chaining mirrorW_leaf / mirrorW_node + IH via
-- binNode_cong (a round-trip / preservation law of exactly the triF kind).

mirrorW_invol : (b : BinM) ->
  Deriv (eqF (ap1 mirrorFW (ap1 mirrorFW (codeB b))) (codeB b))
mirrorW_invol (leafM n) =
  ruleTrans (cong1 mirrorFW (mirrorW_leaf n)) (mirrorW_leaf n)
mirrorW_invol (nodeM n l r) =
  ruleTrans (cong1 mirrorFW (mirrorW_node n (codeB l) (codeB r)))
    (ruleTrans (mirrorW_node n (ap1 mirrorFW (codeB r)) (ap1 mirrorFW (codeB l)))
      (binNode_cong n
        (ap1 mirrorFW (ap1 mirrorFW (codeB l))) (codeB l)
        (ap1 mirrorFW (ap1 mirrorFW (codeB r))) (codeB r)
        (mirrorW_invol l) (mirrorW_invol r)))

------------------------------------------------------------------------
-- SECTION 6.  SEALED public interface.  `mirrorF` is sealed `abstract`;
-- clients see an opaque atom + the equations / preservation lemmas, never
-- the heavy fold body.  `mirrorFW` is the transparent worker.

abstract
  mirrorF : Fun1
  mirrorF = mirrorFW

  mirror_unfold : (t : Term) -> Deriv (eqF (ap1 mirrorF t) (ap1 mirrorFW t))
  mirror_unfold t = axRefl (ap1 mirrorFW t)

mirror_leaf : (n : Term) -> Deriv (eqF (ap1 mirrorF (binLeaf n)) (binLeaf n))
mirror_leaf n = ruleTrans (mirror_unfold (binLeaf n)) (mirrorW_leaf n)

mirror_node : (n l r : Term) ->
  Deriv (eqF (ap1 mirrorF (binNode n l r))
             (binNode n (ap1 mirrorF r) (ap1 mirrorF l)))
mirror_node n l r =
  ruleTrans (mirror_unfold (binNode n l r))
    (ruleTrans (mirrorW_node n l r)
      (binNode_cong n
        (ap1 mirrorFW r) (ap1 mirrorF r)
        (ap1 mirrorFW l) (ap1 mirrorF l)
        (ruleSym (mirror_unfold r)) (ruleSym (mirror_unfold l))))

mirror_wf : (b : BinM) -> Deriv (eqF (ap1 wf (ap1 mirrorF (codeB b))) O)
mirror_wf b = ruleTrans (cong1 wf (mirror_unfold (codeB b))) (mirrorW_wf b)

mirror_invol : (b : BinM) ->
  Deriv (eqF (ap1 mirrorF (ap1 mirrorF (codeB b))) (codeB b))
mirror_invol b =
  ruleTrans (mirror_unfold (ap1 mirrorF (codeB b)))
    (ruleTrans (cong1 mirrorFW (mirror_unfold (codeB b))) (mirrorW_invol b))
