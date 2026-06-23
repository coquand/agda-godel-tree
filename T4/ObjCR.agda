{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ObjCR -- internal Church-Rosser, RE-DERIVED FROM SCRATCH on coded
-- derivation TREES with SIZE / STRUCTURAL induction (the route of
-- HANDOFF-OBJCR-FROM-SCRATCH.md and T4/CON-T0-ARCHITECTURE.md, Theorem A + the
-- diamond).  This DISCARDS the ParCert / isCert / CK / verifyPar / fuel /
-- OpaqueLookup glue: a parallel-reduction derivation is a labelled binary tree
-- whose NODE LABEL carries the constructor tag (0=pZe .. 4=pRS) and whose
-- children are the sub-derivations.
--
--   * `Der`  -- the meta shadow of the coded tree (tag pinned by the
--               constructor, like T4.BinTree.BinM but with the 5 Par tags).
--   * `Red p a b`  -- the STRICT, tag-pinning validity-with-endpoints predicate
--               ("p codes a valid parallel reduction a => b").  Sub-derivations
--               are STRICTLY SMALLER (`Der` is structurally well-founded), so
--               every recursive call below is course-of-values on size(p).
--   * `dev` / `tri`  -- complete development + the triangle map, transcribed
--               clause-for-clause from T4.ChurchRosserProto.
--
-- THE CR CORE (Theorem A, the triangle):
--
--   triPresObj : Red p a b -> Red (tri p) b (dev a)
--
-- proved by STRUCTURAL (= size course-of-values) induction on the derivation,
-- never by an interpreter.  The diamond and `objCR` are then immediate
-- (Theorem A applied twice; apex = dev a).
--
-- This file is the META-over-coded-trees layer.  The genuine object-Deriv
-- connection (lifting `ObjJoin` here to T4.ObjChain.ObjChainM + objJoinClash,
-- Theorem B) and the course-of-values lift to OPAQUE codes (Theorem C) are the
-- documented downstream steps.
--
-- No holes, no postulates, no termination warnings; --safe --without-K
-- --exact-split.

module T4.ObjCR where

open import T4.ChurchRosserProto
  using ( Tm ; ze ; su ; ad
        ; dev
        ; Sigma ; mkSigma ; fst ; snd
        ; And ; mkAnd ; andL ; andR )

------------------------------------------------------------------------
-- SECTION 1.  Derivation TREES (the meta shadow of the coded labelled tree).
--
-- Each constructor is a node tag; arities match the 5 Par constructors:
--   dZe : 0 children       (tag 0)
--   dSu : 1 child          (tag 1)
--   dAd : 2 children       (tag 2)
--   dRO : 1 child          (tag 3)
--   dRS : 2 children       (tag 4)
-- `Der` is structurally well-founded: every recursive call on a child is on a
-- strictly smaller tree -- this IS the "induction on size(p)" of the handoff.

data Der : Set where
  dZe : Der
  dSu : Der -> Der
  dAd : Der -> Der -> Der
  dRO : Der -> Der
  dRS : Der -> Der -> Der

-- A concrete size measure (decoration; the structural recursion below already
-- realises size course-of-values, but this makes the measure tangible and is
-- the bridge to T4.SizedTree.covMeasure for the eventual opaque-code lift).

data Nat : Set where
  zN : Nat
  sN : Nat -> Nat

addN : Nat -> Nat -> Nat
addN zN     m = m
addN (sN n) m = sN (addN n m)

size : Der -> Nat
size dZe       = sN zN
size (dSu p)   = sN (size p)
size (dAd p q) = sN (addN (size p) (size q))
size (dRO p)   = sN (size p)
size (dRS p q) = sN (addN (size p) (size q))

------------------------------------------------------------------------
-- SECTION 2.  The STRICT validity-with-endpoints predicate  Red p a b .
--
-- `Red p a b` holds iff the tree `p` codes a valid parallel reduction a => b.
-- It is tag-pinning: each constructor fixes p's head tag AND the SHAPE of both
-- endpoints, exactly as the strict T4.BinTreeWf.wf pins leaf/node.  This is the
-- validity an ordinary inductive proof silently assumes -- NOT the weak isCert.

data Red : Der -> Tm -> Tm -> Set where
  rdZe : Red dZe ze ze
  rdSu : {p : Der} {t t' : Tm} ->
         Red p t t' -> Red (dSu p) (su t) (su t')
  rdAd : {p q : Der} {a a' b b' : Tm} ->
         Red p a a' -> Red q b b' -> Red (dAd p q) (ad a b) (ad a' b')
  rdRO : {p : Der} {y y' : Tm} ->
         Red p y y' -> Red (dRO p) (ad ze y) y'
  rdRS : {p q : Der} {x x' y y' : Tm} ->
         Red p x x' -> Red q y y' ->
         Red (dRS p q) (ad (su x) y) (su (ad x' y'))

-- Reflexivity:  parRefl as a coded derivation.

reflDer : Tm -> Der
reflDer ze       = dZe
reflDer (su t)   = dSu (reflDer t)
reflDer (ad a b) = dAd (reflDer a) (reflDer b)

redRefl : (t : Tm) -> Red (reflDer t) t t
redRefl ze       = rdZe
redRefl (su t)   = rdSu (redRefl t)
redRefl (ad a b) = rdAd (redRefl a) (redRefl b)

------------------------------------------------------------------------
-- SECTION 3.  The triangle map  tri : Der -> Der  (clause-for-clause from
-- ChurchRosserProto.tri).  Structurally recursive: the dAd dispatch recurses on
-- the LEFT child (a strict subtree), so size strictly decreases.

tri : Der -> Der
tri dZe                  = dZe
tri (dSu p)              = dSu (tri p)
tri (dAd dZe q)          = dRO (tri q)
tri (dAd (dSu p) q)      = dRS (tri p) (tri q)
tri (dAd (dAd p1 p2) q)  = dAd (tri (dAd p1 p2)) (tri q)
tri (dAd (dRO p) q)      = dAd (tri (dRO p)) (tri q)
tri (dAd (dRS p1 p2) q)  = dAd (tri (dRS p1 p2)) (tri q)
tri (dRO p)              = tri p
tri (dRS p q)            = dSu (dAd (tri p) (tri q))

------------------------------------------------------------------------
-- SECTION 4.  THE CR CORE -- Theorem A, the triangle.
--
--   triPresObj : Red p a b -> Red (tri p) b (dev a)
--
-- "For every parallel step p : a => b, the contractum b reduces to dev(a)."
-- Validity AND both endpoints are carried by `Red`, so this single statement IS
-- Theorem A (validity + src/tgt endpoints).  Proved by structural (= size
-- course-of-values) induction on the derivation; mirrors proto `tri`.

triPresObj : {p : Der} {a b : Tm} -> Red p a b -> Red (tri p) b (dev a)
triPresObj rdZe                       = rdZe
triPresObj (rdSu rp)                  = rdSu (triPresObj rp)
triPresObj (rdAd rdZe rq)             = rdRO (triPresObj rq)
triPresObj (rdAd (rdSu rp) rq)        = rdRS (triPresObj rp) (triPresObj rq)
triPresObj (rdAd (rdAd rp1 rp2) rq)   = rdAd (triPresObj (rdAd rp1 rp2)) (triPresObj rq)
triPresObj (rdAd (rdRO rp) rq)        = rdAd (triPresObj (rdRO rp)) (triPresObj rq)
triPresObj (rdAd (rdRS rp1 rp2) rq)   = rdAd (triPresObj (rdRS rp1 rp2)) (triPresObj rq)
triPresObj (rdRO rp)                  = triPresObj rp
triPresObj (rdRS rp rq)               = rdSu (rdAd (triPresObj rp) (triPresObj rq))

------------------------------------------------------------------------
-- SECTION 5.  The DIAMOND -- Theorem A applied twice (apex = dev a).

-- single-step join: a common one-step-Par reduct with a coded leg on each side.
Join1 : Tm -> Tm -> Set
Join1 u1 u2 =
  Sigma Tm (\ w -> And (Sigma Der (\ p -> Red p u1 w))
                       (Sigma Der (\ q -> Red q u2 w)))

objDiamond : {p q : Der} {a u1 u2 : Tm} ->
             Red p a u1 -> Red q a u2 -> Join1 u1 u2
objDiamond {p} {q} {a} rp rq =
  mkSigma (dev a)
    (mkAnd (mkSigma (tri p) (triPresObj rp))
           (mkSigma (tri q) (triPresObj rq)))

------------------------------------------------------------------------
-- SECTION 6.  Multi-step reduction  Reds = Red*  and confluence (strip/tiling).

data Reds : Tm -> Tm -> Set where
  rsdone : {t : Tm} -> Reds t t
  rsmore : {t u v : Tm} (p : Der) -> Red p t u -> Reds u v -> Reds t v

redsTrans : {t u v : Tm} -> Reds t u -> Reds u v -> Reds t v
redsTrans rsdone           ss2 = ss2
redsTrans (rsmore p s ss)  ss2 = rsmore p s (redsTrans ss ss2)

-- a single parallel step is a one-element chain.
red1 : {p : Der} {t u : Tm} -> Red p t u -> Reds t u
red1 {p} r = rsmore p r rsdone

-- strip lemma: a single step against a chain.
strip : {t u v : Tm} {p : Der} ->
        Red p t u -> Reds t v ->
        Sigma Tm (\ w -> And (Reds u w) (Sigma Der (\ r -> Red r v w)))
strip {t} {u} {v} {p} rp rsdone =
  mkSigma u (mkAnd rsdone (mkSigma p rp))
strip rp (rsmore q rq qs) =
  let d  = objDiamond rp rq                       -- common reduct of u, (q's tgt)
      w0 = fst d
      legU = andL (snd d)                          -- Sigma Der (Red _ u w0)
      legM = andR (snd d)                          -- Sigma Der (Red _ (q-tgt) w0)
      rec = strip (snd legM) qs
  in mkSigma (fst rec)
       (mkAnd (rsmore (fst legU) (snd legU) (andL (snd rec)))
              (andR (snd rec)))

-- confluence of  Red* : two chains from t join.
confl : {t v1 v2 : Tm} ->
        Reds t v1 -> Reds t v2 ->
        Sigma Tm (\ w -> And (Reds v1 w) (Reds v2 w))
confl {t} {v1} {v2} rsdone qs = mkSigma v2 (mkAnd qs rsdone)
confl (rsmore p rp ps) qs =
  let s   = strip rp qs                            -- And (Reds u w0) (Red v2-side)
      rec = confl ps (andL (snd s))
  in mkSigma (fst rec)
       (mkAnd (andL (snd rec))
              (rsmore (fst (andR (snd s))) (snd (andR (snd s))) (andR (snd rec))))

------------------------------------------------------------------------
-- SECTION 7.  ObjJoin and the headline  objCR  (the diamond at chain level).
--
-- ObjJoin b c = a common reduct with a  Red*  leg on each side, as in
-- T4.ObjChain (re-stated on the new  Red* , per the handoff).

ObjJoin : Tm -> Tm -> Set
ObjJoin b c = Sigma Tm (\ w -> And (Reds b w) (Reds c w))

-- objCR : two single Par-steps out of a common source join (apex dev a).
objCR : {p q : Der} {a b c : Tm} -> Red p a b -> Red q a c -> ObjJoin b c
objCR {p} {q} {a} rp rq =
  mkSigma (dev a)
    (mkAnd (red1 (triPresObj rp)) (red1 (triPresObj rq)))

-- objConvJoin : confluence of whole reduction sequences (Theorem C combinatorics
-- at this layer; the course-of-values lift to opaque codes is downstream).
objConvJoin : {a v1 v2 : Tm} -> Reds a v1 -> Reds a v2 -> ObjJoin v1 v2
objConvJoin = confl
