{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParConflObj -- the OBJECT-LEVEL CONCLUSIONS of confluence: triangle,
-- diamond and Church-Rosser confluence delivered as genuine BRA  Deriv
-- judgements (object  Par / Pars  derivations), the first step of the
-- OBJECT internalisation of the meta Church-Rosser proof.
--
--   parTriObj  : ParM t u  -> Deriv (Par  (code u) (code (dev t)))   -- triangle
--   diamondObj : ParM t u1 -> ParM t u2  -> DiamondObj u1 u2          -- diamond
--   conflObj   : ParsM t v1 -> ParsM t v2 -> ConflObj v1 v2           -- confluence
--
-- where  DiamondObj / ConflObj  package a common apex  w  together with the
-- two converging reductions as OBJECT derivations  Deriv (Par  (code _)(code w))
-- resp.  Deriv (Pars (code _)(code w)) .  For  ConflObj  the two legs are stored
-- through a SEALED opaque head  PsObj  (= Deriv (Pars ..)  behind an  abstract
-- boundary) and recovered as genuine  Deriv  by the accessors  conflLegL /
-- conflLegR ; this is a PERFORMANCE seal only (see the note on SECTION 3).
--
-- ARCHITECTURE (Thierry-approved, see HANDOFF / T4.ParCertOf).  The confluence
-- COMBINATORICS (triM / stripM / confl) ITERATE the triangle -- a diamond leg
-- is fed into the next diamond -- and a bare object certificate is INERT (no
-- inductive structure to re-develop), so the iteration MUST stay META
-- (T4.ParConfl).  This file does NOT re-do that induction; it APPLIES the meta
-- result and pushes its CONCLUSIONS into the object world through the
-- certificate->derivation lifts  parIntro (T4.ParIntro) and  parsObjOf
-- (T4.ParsObj).  The apex  w = dev t  resp.  car (confl ..)  is a concrete
-- coded term; both output reductions are real  Deriv .  No holes, no
-- postulates.

module T4.ParConflObj where

open import T4.Base

open import T4.ParReflPres using ( Tm ; code )
open import T4.ParTri      using ( ParM ; dev ; tri )
open import T4.ParConfl    using
  ( ParsM ; confl ; Sg ; car ; prf ; Conj ; prjL ; prjR )
open import T4.ParIntro    using ( Par ; parIntro )
open import T4.ParsObj     using ( Pars ; parsObjOf )

------------------------------------------------------------------------
-- SECTION 1.  The object TRIANGLE.
--   For every parallel step  ParM t u ,  u  parallel-reduces (one object
--   Par step) to the complete development  dev t :
--     parTriObj t u p : Deriv (Par (code u) (code (dev t))) .
--   (= parIntro applied to the meta triangle certificate  T4.ParTri.tri .)

parTriObj : (t uu : Tm) -> ParM t uu -> Deriv (Par (code uu) (code (dev t)))
parTriObj t uu p = parIntro uu (dev t) (tri p)

------------------------------------------------------------------------
-- SECTION 2.  The object DIAMOND.
--   Any two parallel steps out of  t  meet at the apex  dev t , both legs
--   being object  Par  derivations.

record DiamondObj (u1 u2 : Tm) : Set where
  constructor mkDiamondObj
  field
    apex : Tm
    legL : Deriv (Par (code u1) (code apex))
    legR : Deriv (Par (code u2) (code apex))
open DiamondObj public

diamondObj : {t u1 u2 : Tm} -> ParM t u1 -> ParM t u2 -> DiamondObj u1 u2
diamondObj {t} {u1} {u2} p1 p2 =
  mkDiamondObj (dev t) (parTriObj t u1 p1) (parTriObj t u2 p2)

------------------------------------------------------------------------
-- SECTION 3.  Object CHURCH-ROSSER (confluence) over multi-step reduction.
--   Any two reduction sequences out of  t  converge: there is an apex  w
--   and OBJECT multi-step derivations  Deriv (Pars (code v1)(code w)) ,
--   Deriv (Pars (code v2)(code w)) .
--
--   The witness apex and the meta multi-steps come from the meta  confl
--   (T4.ParConfl); each meta  ParsM  leaf is lifted to an object  Pars
--   derivation by  parsObjOf (T4.ParsObj).
--
--   PERFORMANCE NOTE (see [[feedback-agda-abstract-seal-avoid-forcing]]).
--   Storing the legs DIRECTLY as  Deriv (Pars (code v1)(code apex))  in the
--   dependent record makes the constructor application re-normalise the heavy
--   multi-step body of  Pars  (isChain / parsSrc / parsTgt) once  apex  is
--   substituted -- the conversion checker stops short-circuiting on syntax and
--   walks the whole transparent value, blowing past the 20s budget (the
--   single-step  Par  of SECTION 2 is light enough to stay fast as a plain
--   record).  So the  Pars  legs are sealed behind the  abstract  head  PsObj :
--   the constructor then compares only the spine (v1 , apex) syntactically.
--   The seal is DEFINITIONAL ( PsObj v w = Deriv (Pars (code v)(code w)) ); the
--   genuine  Deriv  is recovered verbatim by  conflLegL / conflLegR  through the
--   un-seal  unPsObj .

abstract
  PsObj : Tm -> Tm -> Set
  PsObj vv ww = Deriv (Pars (code vv) (code ww))

  mkPsObj : (vv ww : Tm) -> Deriv (Pars (code vv) (code ww)) -> PsObj vv ww
  mkPsObj vv ww d = d

  unPsObj : (vv ww : Tm) -> PsObj vv ww -> Deriv (Pars (code vv) (code ww))
  unPsObj vv ww d = d

record ConflObj (v1 v2 : Tm) : Set where
  constructor mkConflObj
  field
    apex : Tm
    legL : PsObj v1 apex
    legR : PsObj v2 apex
open ConflObj public

conflObj : {t v1 v2 : Tm} -> ParsM t v1 -> ParsM t v2 -> ConflObj v1 v2
conflObj {t} {v1} {v2} ps1 ps2 = go (confl ps1 ps2)
  where
    go : Sg (\ w -> Conj (ParsM v1 w) (ParsM v2 w)) -> ConflObj v1 v2
    go r = mkConflObj (car r)
             (mkPsObj v1 (car r) (parsObjOf v1 (car r) (prjL (prf r))))
             (mkPsObj v2 (car r) (parsObjOf v2 (car r) (prjR (prf r))))

-- Genuine-Deriv accessors: the two converging multi-step reductions as
-- real BRA object derivations  Deriv (Pars ..) .

conflLegL : {v1 v2 : Tm} (c : ConflObj v1 v2) ->
            Deriv (Pars (code v1) (code (apex c)))
conflLegL {v1} {v2} c = unPsObj v1 (apex c) (legL c)

conflLegR : {v1 v2 : Tm} (c : ConflObj v1 v2) ->
            Deriv (Pars (code v2) (code (apex c)))
conflLegR {v1} {v2} c = unPsObj v2 (apex c) (legR c)
