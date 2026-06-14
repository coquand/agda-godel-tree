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
-- resp.  Deriv (Pars (code _)(code w)) .
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
--
-- ABSTRACTION / 20s BUDGET NOTE.  The apex-and-two-legs package is expressed
-- with the EXISTING combinators  Sg (B : Tm -> Set)  and  Conj  (T4.ParConfl),
-- NOT a bespoke dependent record  record { apex : Tm ; legL : Deriv (.. apex) ;
-- legR : Deriv (.. apex) } .  A bespoke record whose later fields mention the
-- earlier  apex  field forces Agda to renormalise the (large) object formula
--   Pars (code v1) (code apex)   while elaborating the constructor, which blows
-- the type-checking budget.  The  Sg/Conj  form (witness  Tm  +  B  applied
-- to it) does the field comparison syntactically and stays well under 20s.
-- The two legs are read off with  car / prf / prjL / prjR .

module T4.ParConflObj where

open import T4.Base

open import T4.ParReflPres using ( Tm ; code )
open import T4.ParTri      using ( ParM ; dev ; tri )
open import T4.ParConfl    using
  ( ParsM ; confl ; Sg ; mkSg ; car ; prf ; Conj ; mkConj ; prjL ; prjR )
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
--   being object  Par  derivations.  Packaged as
--     Sg (\ w -> Conj (Deriv (Par (code u1)(code w)))
--                     (Deriv (Par (code u2)(code w)))) ;
--   the apex is  car  and the two legs  prjL (prf _) / prjR (prf _) .

DiamondObj : Tm -> Tm -> Set
DiamondObj u1 u2 =
  Sg (\ w -> Conj (Deriv (Par (code u1) (code w)))
                  (Deriv (Par (code u2) (code w))))

diamondObj : {t u1 u2 : Tm} -> ParM t u1 -> ParM t u2 -> DiamondObj u1 u2
diamondObj {t} {u1} {u2} p1 p2 =
  mkSg (dev t) (mkConj (parTriObj t u1 p1) (parTriObj t u2 p2))

------------------------------------------------------------------------
-- SECTION 3.  Object CHURCH-ROSSER (confluence) over multi-step reduction.
--   Any two reduction sequences out of  t  converge: there is an apex  w
--   and OBJECT multi-step derivations  Deriv (Pars (code v1)(code w)) ,
--   Deriv (Pars (code v2)(code w)) .
--
--   The witness apex and the meta multi-steps come from the meta  confl
--   (T4.ParConfl); each meta  ParsM  leaf is lifted to an object  Pars
--   derivation by  parsObjOf (T4.ParsObj).

ConflObj : Tm -> Tm -> Set
ConflObj v1 v2 =
  Sg (\ w -> Conj (Deriv (Pars (code v1) (code w)))
                  (Deriv (Pars (code v2) (code w))))

conflObj : {t v1 v2 : Tm} -> ParsM t v1 -> ParsM t v2 -> ConflObj v1 v2
conflObj {t} {v1} {v2} ps1 ps2 =
  let r = confl ps1 ps2 in
  mkSg (car r)
       (mkConj (parsObjOf v1 (car r) (prjL (prf r)))
               (parsObjOf v2 (car r) (prjR (prf r))))
