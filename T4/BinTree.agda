{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BinTree -- a reusable BRA library for CODED LABELLED BINARY TREES with
-- a structural induction principle and definition of functions by PRIMITIVE
-- RECURSION (attempt3 §14 "THE NEXT FOUNDATION").
--
-- The data type (labels are arbitrary object Terms; specialise to Nat via
-- natCode if you want  Bin = Atom Nat | Branch Bin Bin):
--
--     Bin = Leaf Term | Node Term Bin Bin
--
-- Object coding (UNIFORMLY tagged pairs, same scheme as T4.TrsCodeObj /
-- T4.ParsObj; tags are SUCCESSORS so every code is a fold NODE  pi (s _) _):
--
--     binLeaf n      = Pair (natCode 1) n                       (tag 1)
--     binNode n l r  = Pair (natCode 2) (Pair n (Pair l r))     (tag 2)
--
-- Projectors  binTag / binArg / binLab / binL / binR  with their Deriv
-- equations (from axFst / axSnd only -- no induction; this is the
-- constructor/decoder interface).
--
-- The KEY new piece over T4.ParsObj (which only recurses on the RIGHT child
-- of a list cons): a node-plumbing recovery for BOTH children -- the left
-- child  l = Fst (Snd payload)  and the right child  r = Snd (Snd payload)
-- are each bounded  leq _ P_outer  (via leq_pi_left / leq_pi_right) and so
-- their recursive fold values are recovered by  np_lookup_gen .  This makes
-- the binary recursor  binRec  a genuine structural recursor.
--
-- We demonstrate the engine with a real primitive-recursive function over
-- the type -- the well-formedness predicate  isWfW : Fun1  -- and its two
-- defining equations as  Deriv :
--
--     isWfW (binLeaf n)     = O                       (a leaf is wf)
--     isWfW (binNode n l r) = pi (isWfW l) (isWfW r)    (= O iff both children wf)
--
-- isWfW_node uses BOTH recursive calls, so it exercises the binary recovery.
--
-- The META layer carries the tree structure (data BinM + codeB), giving the
-- structural INDUCTION principle  binInd  for free (Agda recursion), exactly
-- as T4.ParReflPres carries  Tm .  The payoff (attempt3 §14: "preservation =
-- one structural induction") is shown by  isWfW_code : every coded well-formed
-- tree validates, proved by ONE meta induction chaining the defining eqs.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.BinTree where

open import T4.Base

open import T4.FoldRec   using ( lookupAt )
open import T4.ParsObj   using ( foldOf ; test1 ; module NP )
open import T4.LenR      using ( get_rc )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.ParEnds   using ( pi_O_O )

open import BRA3.Church       using ( pi )
open import BRA3.ChurchLeq    using ( leq )
open import BRA3.PairAlgebra  using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )

------------------------------------------------------------------------
-- SECTION 0.  Object coding.

binLeaf : Term -> Term
binLeaf n = ap2 Pair (natCode 1) n

binNode : Term -> Term -> Term -> Term
binNode n l r = ap2 Pair (natCode 2) (ap2 Pair n (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 1.  Projectors and their Deriv equations (axFst / axSnd only).

binTag : Term -> Term            -- the constructor tag
binTag d = ap1 Fst d

binArg : Term -> Term            -- the argument bundle
binArg d = ap1 Snd d

binTag_leaf : (n : Term) -> Deriv (eqF (binTag (binLeaf n)) (natCode 1))
binTag_leaf n = axFst (natCode 1) n

binArg_leaf : (n : Term) -> Deriv (eqF (binArg (binLeaf n)) n)
binArg_leaf n = axSnd (natCode 1) n

binTag_node : (n l r : Term) -> Deriv (eqF (binTag (binNode n l r)) (natCode 2))
binTag_node n l r = axFst (natCode 2) (ap2 Pair n (ap2 Pair l r))

binArg_node : (n l r : Term) ->
  Deriv (eqF (binArg (binNode n l r)) (ap2 Pair n (ap2 Pair l r)))
binArg_node n l r = axSnd (natCode 2) (ap2 Pair n (ap2 Pair l r))

-- node label  n = Fst (Snd code)
binLab : (n l r : Term) -> Deriv (eqF (ap1 Fst (binArg (binNode n l r))) n)
binLab n l r = ruleTrans (cong1 Fst (binArg_node n l r)) (axFst n (ap2 Pair l r))

-- left child  l = Fst (Snd (Snd code))
binL : (n l r : Term) ->
  Deriv (eqF (ap1 Fst (ap1 Snd (binArg (binNode n l r)))) l)
binL n l r =
  ruleTrans (cong1 Fst (cong1 Snd (binArg_node n l r)))
    (ruleTrans (cong1 Fst (axSnd n (ap2 Pair l r))) (axFst l r))

-- right child  r = Snd (Snd (Snd code))
binR : (n l r : Term) ->
  Deriv (eqF (ap1 Snd (ap1 Snd (binArg (binNode n l r)))) r)
binR n l r =
  ruleTrans (cong1 Snd (cong1 Snd (binArg_node n l r)))
    (ruleTrans (cong1 Snd (axSnd n (ap2 Pair l r))) (axSnd l r))

------------------------------------------------------------------------
-- SECTION 2.  Child-index Fun1s (read the children out of a fold package).
--
-- Inside a fold node package  input_pkg ,  get_rc input_pkg = payload .
-- For a  binNode  the payload is  Pair n (Pair l r) , so:
--     nIdx -> n = Fst payload
--     lIdx -> l = Fst (Snd payload)
--     rIdx -> r = Snd (Snd payload)

nIdx : Fun1
nIdx = compose1U Fst get_rc

lIdx : Fun1
lIdx = compose1U Fst (compose1U Snd get_rc)

rIdx : Fun1
rIdx = compose1U Snd (compose1U Snd get_rc)

------------------------------------------------------------------------
-- SECTION 3.  The binary recursor  binRec  and a sample fold  isWfW .
--
--   binRec g cellLeaf cellNode = foldOf g cellLeaf cellNode
--     -- cellLeaf fires on a leaf package, cellNode on a node package.
-- The node cell may read  nIdx / lIdx / rIdx  and the two recursive values
--   lookupAt lIdx / lookupAt rIdx  (recovered below).

binRec : Fun1 -> Fun1 -> Fun1 -> Fun1
binRec g cellLeaf cellNode = foldOf g cellLeaf cellNode

------------------------------------------------------------------------
-- isWfW : the well-formedness predicate (a real primitive-recursive function).

cellLeafWf : Fun1
cellLeafWf = Z                                         -- leaf -> O

cellNodeWf : Fun1
cellNodeWf = C pi (lookupAt lIdx) (lookupAt rIdx)      -- node -> pi (isWfW l)(isWfW r)

isWfW : Fun1
isWfW = binRec Z cellLeafWf cellNodeWf

------------------------------------------------------------------------
-- isWfW_leaf :  isWfW (binLeaf n) = O .

isWfW_leaf : (n : Term) -> Deriv (eqF (ap1 isWfW (binLeaf n)) O)
isWfW_leaf n =
  let open NP Z cellLeafWf cellNodeWf O n
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (axZ input_pkg)   -- cellLeafWf = Z -> O

------------------------------------------------------------------------
-- isWfW_node :  isWfW (binNode n l r) = pi (isWfW l) (isWfW r) .
-- This is the BOTH-children recovery (the new engine).

isWfW_node : (n l r : Term) ->
  Deriv (eqF (ap1 isWfW (binNode n l r))
             (ap2 pi (ap1 isWfW l) (ap1 isWfW r)))
isWfW_node n l r =
  let open NP Z cellLeafWf cellNodeWf (natCode 1) (ap2 Pair n (ap2 Pair l r))

      -- node tag = 2 != 1, so the leaf test SKIPS -> the node cell fires.
      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      -- payload  =  Snd (get_rc input_pkg)  =  Pair l r .
      sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair l r))
      sndArg_eq =
        ruleTrans (compose1U_eq Snd get_rc input_pkg)
          (ruleTrans (cong1 Snd np_rc) (axSnd n (ap2 Pair l r)))

      -- lIdx input_pkg = Fst (Pair l r) = l .
      lIdx_eq : Deriv (eqF (ap1 lIdx input_pkg) l)
      lIdx_eq =
        ruleTrans (compose1U_eq Fst (compose1U Snd get_rc) input_pkg)
          (ruleTrans (cong1 Fst sndArg_eq) (axFst l r))

      -- rIdx input_pkg = Snd (Pair l r) = r .
      rIdx_eq : Deriv (eqF (ap1 rIdx input_pkg) r)
      rIdx_eq =
        ruleTrans (compose1U_eq Snd (compose1U Snd get_rc) input_pkg)
          (ruleTrans (cong1 Snd sndArg_eq) (axSnd l r))

      -- both children are <= P_outer (the strict-decrease bounds).
      leq_lr_P : Deriv (leq (ap2 Pair l r) P_outer)
      leq_lr_P = leq_trans (ap2 Pair l r) (ap2 Pair n (ap2 Pair l r)) P_outer
                   (leq_pi_right n (ap2 Pair l r)) leq_b_P
      leq_l_P : Deriv (leq l P_outer)
      leq_l_P = leq_trans l (ap2 Pair l r) P_outer (leq_pi_left l r) leq_lr_P
      leq_r_P : Deriv (leq r P_outer)
      leq_r_P = leq_trans r (ap2 Pair l r) P_outer (leq_pi_right l r) leq_lr_P

      -- recover the two recursive calls.
      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 isWfW l))
      recL = np_lookup_gen lIdx l lIdx_eq leq_l_P
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 isWfW r))
      recR = np_lookup_gen rIdx r rIdx_eq leq_r_P

      -- cellNodeWf input_pkg = pi (isWfW l) (isWfW r) .
      cellNodeWf_val :
        Deriv (eqF (ap1 cellNodeWf input_pkg) (ap2 pi (ap1 isWfW l) (ap1 isWfW r)))
      cellNodeWf_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 isWfW l) recR))
  in ruleTrans (collapse_snd t1_O) cellNodeWf_val

------------------------------------------------------------------------
-- SECTION 4.  The META layer:  data BinM + codeB + induction principle.

data BinM : Set where
  leafM : Term -> BinM
  nodeM : Term -> BinM -> BinM -> BinM

codeB : BinM -> Term
codeB (leafM n)     = binLeaf n
codeB (nodeM n l r) = binNode n (codeB l) (codeB r)

-- the structural INDUCTION / RECURSION principle (Agda recursion).
binInd :
  (P : BinM -> Set) ->
  ((n : Term) -> P (leafM n)) ->
  ((n : Term) (l r : BinM) -> P l -> P r -> P (nodeM n l r)) ->
  (b : BinM) -> P b
binInd P pl pn (leafM n)     = pl n
binInd P pl pn (nodeM n l r) = pn n l r (binInd P pl pn l) (binInd P pl pn r)

------------------------------------------------------------------------
-- SECTION 5.  Payoff: every coded well-formed tree validates.
-- "preservation = ONE structural induction" -- meta induction on BinM
-- chaining the two defining equations + pi_O_O.

isWfW_code : (b : BinM) -> Deriv (eqF (ap1 isWfW (codeB b)) O)
isWfW_code (leafM n) = isWfW_leaf n
isWfW_code (nodeM n l r) =
  ruleTrans (isWfW_node n (codeB l) (codeB r))
    (ruleTrans (congL pi (ap1 isWfW (codeB r)) (isWfW_code l))
      (ruleTrans (congR pi O (isWfW_code r)) pi_O_O))

------------------------------------------------------------------------
-- SECTION 6.  SEALED public interface.  `isWf` is sealed `abstract`, so
-- downstream clients see it as an OPAQUE atom plus the equations below --
-- the conversion checker never walks the heavy fold body (cf. the
-- abstract-seal recipe).  `isWfW` is the transparent worker; the equations
-- are re-exported through the  isWf_unfold  bridge.

abstract
  isWf : Fun1
  isWf = isWfW

  isWf_unfold : (t : Term) -> Deriv (eqF (ap1 isWf t) (ap1 isWfW t))
  isWf_unfold t = axRefl (ap1 isWfW t)

isWf_leaf : (n : Term) -> Deriv (eqF (ap1 isWf (binLeaf n)) O)
isWf_leaf n = ruleTrans (isWf_unfold (binLeaf n)) (isWfW_leaf n)

isWf_node : (n l r : Term) ->
  Deriv (eqF (ap1 isWf (binNode n l r)) (ap2 pi (ap1 isWf l) (ap1 isWf r)))
isWf_node n l r =
  ruleTrans (isWf_unfold (binNode n l r))
    (ruleTrans (isWfW_node n l r)
      (ruleTrans (congL pi (ap1 isWfW r) (ruleSym (isWf_unfold l)))
                 (congR pi (ap1 isWf l) (ruleSym (isWf_unfold r)))))

isWf_code : (b : BinM) -> Deriv (eqF (ap1 isWf (codeB b)) O)
isWf_code b = ruleTrans (isWf_unfold (codeB b)) (isWfW_code b)
