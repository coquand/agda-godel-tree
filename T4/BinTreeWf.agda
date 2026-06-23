{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.BinTreeWf -- STRICT, TAG-PINNING well-formedness for coded binary
-- trees (attempt3 §14: "a wfW/shape predicate on codes that DOES pin the
-- constructor").
--
-- T4.BinTree.isWf treats EVERY non-leaf (tag != 1) as a node, so a junk
-- code with tag >= 3 is silently validated.  Here  wfW : Fun1  is a 3-WAY
-- dispatch that ACCEPTS only the two real constructors and REJECTS any other
-- tag:
--
--     wfW (binLeaf n)      = O                      -- valid leaf
--     wfW (binNode n l r)  = pi (wfW l) (wfW r)       -- valid iff both children wfW
--     wfW (binJunk3 n l r) = s O                    -- tag 3 -> nonzero = INVALID
--
-- The third equation is the pinning content: a tag-3 "node" does NOT
-- validate.  Crisply:  wfW_junk3_neg : neg (wfW (binJunk3 n l r) = O)  (via
-- ax_succ_nonzero), the object proof that wfW rejects the junk shape.
--
-- The 3-way fold = the proven 2-way  foldOf / NP  engine (leaf vs rest)
-- with the "rest" cell an INNER condFork on a second tag test (node vs junk).
--
-- ON OPAQUE-CODE INVERSION.  A full object inversion
--     wfW d = O  ->  d = binLeaf .. OR d = binNode .. (with smaller wfW children)
-- for an ARBITRARY opaque term  d  needs the surjective Cantor-pairing law
-- pi (Fst d) (Snd d) = d , which is NOT available in this repo.  The usable
-- substitute is the META tree layer  T4.BinTree.BinM / codeB / binInd : carry
-- the structure at the meta level (every code we ever handle is  codeB b  for
-- a known  b : BinM ), and structural inversion/recursion is  binInd .  The
-- payoff lemma  wfW_code  below is that meta induction; T4.BinTreeDev uses the
-- same route so cert preservation is one  binInd .
--
-- No holes, no postulates, no termination warnings.

module T4.BinTreeWf where

open import T4.Base

open import T4.BinTree   using ( binLeaf ; binNode ; lIdx ; rIdx
                               ; BinM ; leafM ; nodeM ; codeB )
open import T4.FoldRec   using ( lookupAt )
open import T4.ParsObj   using ( foldOf ; test1 ; module NP )
open import T4.LenR      using ( get_rc )
open import T4.LeqPiLeft using ( leq_pi_left )
open import T4.LeqMono   using ( leq_pi_right ; leq_trans )
open import T4.ProgParse using ( get_tag )
open import T4.ParEnds   using ( pi_O_O )

open import BRA3.Church        using ( pi )
open import BRA3.ChurchLeq     using ( leq )
open import BRA3.PairAlgebra   using ( compose1U_eq )
open import BRA3.SubT.NatEq    using ( natEqF ; natEq_eq )
open import BRA3.SubT.V2NatNeq using ( NatNeqWitness ; natEqF_at_neq ; decideNatNeq )
open import BRA3.Classical     using ( axContrapos )

------------------------------------------------------------------------
-- SECTION 0.  A junk code (tag 3) used to exhibit rejection.

binJunk3 : Term -> Term -> Term -> Term
binJunk3 n l r = ap2 Pair (natCode 3) (ap2 Pair n (ap2 Pair l r))

------------------------------------------------------------------------
-- SECTION 1.  The strict predicate  wfW  (3-way: leaf | node | junk).

test2 : Fun1                                       -- tag == 2 ?
test2 = C natEqF get_tag (constN 2)

cellLeafW : Fun1
cellLeafW = Z                                      -- leaf -> O

cellNodeW : Fun1
cellNodeW = C pi (lookupAt lIdx) (lookupAt rIdx)   -- node -> pi (wfW l)(wfW r)

cellJunkW : Fun1
cellJunkW = constN 1                               -- junk -> s O  (nonzero)

-- the "rest" cell: an inner fork  node (tag==2) vs junk (else).
innerW : Fun1
innerW = C condFork (C pi cellNodeW cellJunkW) test2

wfW : Fun1
wfW = foldOf Z cellLeafW innerW

------------------------------------------------------------------------
-- SECTION 2.  wfW_leaf :  wfW (binLeaf n) = O .

wfW_leaf : (n : Term) -> Deriv (eqF (ap1 wfW (binLeaf n)) O)
wfW_leaf n =
  let open NP Z cellLeafW innerW O n
      t1_fire : Deriv (eqF (ap1 test1 input_pkg) (ap1 s O))
      t1_fire = ruleTrans test1_val (natEq_eq 1)
  in ruleTrans (collapse_fst t1_fire) (axZ input_pkg)

------------------------------------------------------------------------
-- SECTION 3.  Shared "rest"-branch evaluation (tag != 1; the inner fork).
-- Given the leaf test SKIPS, wfW node = innerW input_pkg ; this module
-- evaluates the inner fork from the second tag test's value.

module Rest (A b : Term) where
  open NP Z cellLeafW innerW A b public

  pairCell2 : Term
  pairCell2 = ap1 (C pi cellNodeW cellJunkW) input_pkg

  fst_pairCell2 : Deriv (eqF (ap1 Fst pairCell2) (ap1 cellNodeW input_pkg))
  fst_pairCell2 =
    ruleTrans (cong1 Fst (ax_C pi cellNodeW cellJunkW input_pkg))
              (axFst (ap1 cellNodeW input_pkg) (ap1 cellJunkW input_pkg))
  snd_pairCell2 : Deriv (eqF (ap1 Snd pairCell2) (ap1 cellJunkW input_pkg))
  snd_pairCell2 =
    ruleTrans (cong1 Snd (ax_C pi cellNodeW cellJunkW input_pkg))
              (axSnd (ap1 cellNodeW input_pkg) (ap1 cellJunkW input_pkg))

  inner_unfold : Deriv (eqF (ap1 innerW input_pkg)
                            (ap2 condFork pairCell2 (ap1 test2 input_pkg)))
  inner_unfold = ax_C condFork (C pi cellNodeW cellJunkW) test2 input_pkg

  -- the second test's value =  natEqF (s A) (natCode 2) .
  test2_val : Deriv (eqF (ap1 test2 input_pkg) (ap2 natEqF (ap1 s A) (natCode 2)))
  test2_val =
    ruleTrans (ax_C natEqF get_tag (constN 2) input_pkg)
      (ruleTrans (congL natEqF (ap1 (constN 2) input_pkg) np_head)
                 (congR natEqF (ap1 s A) (constN_eq 2 input_pkg)))

  -- node branch: inner fork FIRES (test2 = s O) -> cellNodeW.
  inner_node : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O)) ->
               Deriv (eqF (ap1 innerW input_pkg) (ap1 cellNodeW input_pkg))
  inner_node t2_fire =
    ruleTrans inner_unfold
      (ruleTrans (congR condFork pairCell2 t2_fire)
        (ruleTrans (condFork_true_nc pairCell2 O) fst_pairCell2))

  -- junk branch: inner fork SKIPS (test2 = O) -> cellJunkW.
  inner_junk : Deriv (eqF (ap1 test2 input_pkg) O) ->
               Deriv (eqF (ap1 innerW input_pkg) (ap1 cellJunkW input_pkg))
  inner_junk t2_O =
    ruleTrans inner_unfold
      (ruleTrans (congR condFork pairCell2 t2_O)
        (ruleTrans (condFork_false pairCell2) snd_pairCell2))

------------------------------------------------------------------------
-- SECTION 4.  wfW_node :  wfW (binNode n l r) = pi (wfW l) (wfW r) .

wfW_node : (n l r : Term) ->
  Deriv (eqF (ap1 wfW (binNode n l r))
             (ap2 pi (ap1 wfW l) (ap1 wfW r)))
wfW_node n l r =
  let open Rest (natCode 1) (ap2 Pair n (ap2 Pair l r))

      w21 : NatNeqWitness 2 1
      w21 = decideNatNeq 2 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 2 1 w21)

      -- inner fork fires:  tag = 2 .
      t2_fire : Deriv (eqF (ap1 test2 input_pkg) (ap1 s O))
      t2_fire = ruleTrans test2_val (natEq_eq 2)

      -- children extraction + bounds (binary recovery, as T4.BinTree).
      sndArg_eq : Deriv (eqF (ap1 (compose1U Snd get_rc) input_pkg) (ap2 Pair l r))
      sndArg_eq =
        ruleTrans (compose1U_eq Snd get_rc input_pkg)
          (ruleTrans (cong1 Snd np_rc) (axSnd n (ap2 Pair l r)))
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

      recL : Deriv (eqF (ap1 (lookupAt lIdx) input_pkg) (ap1 wfW l))
      recL = np_lookup_gen lIdx l lIdx_eq leq_l_P
      recR : Deriv (eqF (ap1 (lookupAt rIdx) input_pkg) (ap1 wfW r))
      recR = np_lookup_gen rIdx r rIdx_eq leq_r_P

      cellNodeW_val :
        Deriv (eqF (ap1 cellNodeW input_pkg) (ap2 pi (ap1 wfW l) (ap1 wfW r)))
      cellNodeW_val =
        ruleTrans (ax_C pi (lookupAt lIdx) (lookupAt rIdx) input_pkg)
          (ruleTrans (congL pi (ap1 (lookupAt rIdx) input_pkg) recL)
                     (congR pi (ap1 wfW l) recR))
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans (inner_node t2_fire) cellNodeW_val)

------------------------------------------------------------------------
-- SECTION 5.  wfW_junk3 :  wfW (binJunk3 n l r) = s O  (= INVALID).

wfW_junk3 : (n l r : Term) -> Deriv (eqF (ap1 wfW (binJunk3 n l r)) (ap1 s O))
wfW_junk3 n l r =
  let open Rest (natCode 2) (ap2 Pair n (ap2 Pair l r))

      w31 : NatNeqWitness 3 1
      w31 = decideNatNeq 3 1 (\ ())
      t1_O : Deriv (eqF (ap1 test1 input_pkg) O)
      t1_O = ruleTrans test1_val (natEqF_at_neq 3 1 w31)

      -- inner fork SKIPS:  tag = 3 != 2 .
      w32 : NatNeqWitness 3 2
      w32 = decideNatNeq 3 2 (\ ())
      t2_O : Deriv (eqF (ap1 test2 input_pkg) O)
      t2_O = ruleTrans test2_val (natEqF_at_neq 3 2 w32)

      junk_val : Deriv (eqF (ap1 cellJunkW input_pkg) (ap1 s O))
      junk_val = constN_eq 1 input_pkg            -- constN 1 = natCode 1 = s O
  in ruleTrans (collapse_snd t1_O)
       (ruleTrans (inner_junk t2_O) junk_val)

------------------------------------------------------------------------
-- SECTION 6.  Object rejection: wfW does NOT validate the junk shape.
--   wfW_junk3_neg :  neg (wfW (binJunk3 n l r) = O)   (via ax_succ_nonzero).

wfW_junk3_neg : (n l r : Term) ->
  Deriv (neg (eqF (ap1 wfW (binJunk3 n l r)) O))
wfW_junk3_neg n l r =
  let a : Term
      a = ap1 wfW (binJunk3 n l r)
      H : Formula
      H = eqF a O
      Q : Formula                                 -- ax_succ_nonzero negates Q
      Q = eqF (ap1 s O) O
      -- imp H Q :  a = O  ->  s O = O   (since a = s O).
      -- ax_eqTrans a (s O) O : (a = s O) -> (a = O) -> (s O = O).
      impHQ : Deriv (imp H Q)
      impHQ = mp (ax_eqTrans a (ap1 s O) O) (wfW_junk3 n l r)
  in mp (mp (axContrapos H Q) impHQ) ax_succ_nonzero

------------------------------------------------------------------------
-- SECTION 7.  Payoff: every coded well-formed tree validates  (meta
-- induction on BinM = the structural induction principle, chaining the two
-- positive equations + pi_O_O).  This is the inversion principle's usable
-- form: structure carried by BinM, "preservation = one binInd".

wfW_code : (b : BinM) -> Deriv (eqF (ap1 wfW (codeB b)) O)
wfW_code (leafM n) = wfW_leaf n
wfW_code (nodeM n l r) =
  ruleTrans (wfW_node n (codeB l) (codeB r))
    (ruleTrans (congL pi (ap1 wfW (codeB r)) (wfW_code l))
      (ruleTrans (congR pi O (wfW_code r)) pi_O_O))

------------------------------------------------------------------------
-- SECTION 8.  SEALED public interface.  `wf` is sealed `abstract`; clients
-- see an opaque atom + the equations, never the heavy 3-way fold body.
-- `wfW` is the transparent worker.

abstract
  wf : Fun1
  wf = wfW

  wf_unfold : (t : Term) -> Deriv (eqF (ap1 wf t) (ap1 wfW t))
  wf_unfold t = axRefl (ap1 wfW t)

wf_leaf : (n : Term) -> Deriv (eqF (ap1 wf (binLeaf n)) O)
wf_leaf n = ruleTrans (wf_unfold (binLeaf n)) (wfW_leaf n)

wf_node : (n l r : Term) ->
  Deriv (eqF (ap1 wf (binNode n l r)) (ap2 pi (ap1 wf l) (ap1 wf r)))
wf_node n l r =
  ruleTrans (wf_unfold (binNode n l r))
    (ruleTrans (wfW_node n l r)
      (ruleTrans (congL pi (ap1 wfW r) (ruleSym (wf_unfold l)))
                 (congR pi (ap1 wf l) (ruleSym (wf_unfold r)))))

wf_junk3 : (n l r : Term) -> Deriv (eqF (ap1 wf (binJunk3 n l r)) (ap1 s O))
wf_junk3 n l r = ruleTrans (wf_unfold (binJunk3 n l r)) (wfW_junk3 n l r)

wf_junk3_neg : (n l r : Term) ->
  Deriv (neg (eqF (ap1 wf (binJunk3 n l r)) O))
wf_junk3_neg n l r =
  let a : Term
      a = ap1 wf (binJunk3 n l r)
      H : Formula
      H = eqF a O
      Q : Formula
      Q = eqF (ap1 s O) O
      impHQ : Deriv (imp H Q)
      impHQ = mp (ax_eqTrans a (ap1 s O) O) (wf_junk3 n l r)
  in mp (mp (axContrapos H Q) impHQ) ax_succ_nonzero

wf_code : (b : BinM) -> Deriv (eqF (ap1 wf (codeB b)) O)
wf_code b = ruleTrans (wf_unfold (codeB b)) (wfW_code b)
