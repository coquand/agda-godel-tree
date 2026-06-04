{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.SurpriseG2ConjConcrete -- the THIN concrete wireup of
-- the conjunction-shape surprise-G2 theorem at the BerryDataConj input
-- shape  (per Step 5 of  T4/NEXT-SESSION-CGICONJ-RESIDUAL-B.md).
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- `surpriseG2ConjConcrete`  --  the surprise-G2 theorem in its FULLY
-- DATA-PARAMETRIC concrete form :
--
--   (consts  : SurpriseConstsConj)
--   (descFam : DescFamConj consts)
--   (bData   : BerryDataConj M enum)
--   (conInt  : ConOpenInt)
--   ----------------------------------------------------------------
--   Deriv (eqF O (ap1 s O))
--
-- The CGIConjSpec parameter of  surpriseG2ConjFromDescFam  is no longer
-- abstract :  it is built from the BerryDataConj  enumeration pin via
-- `cgiConjBody`  ( T4.SurpriseG2.CGIConjBody ) , which discharges the
-- full Berry-clash chain ( DischargeKdefConj + ChainKdefConj +
-- CgiClashConj ) internally.
--
-- =====================================================================
-- WHAT IS DEFERRED  (THE FINAL TWO RESIDUALS).
-- =====================================================================
--
-- 1.  `DescFamConj consts`  --  the per-day "describes" derivations
--     (one  Deriv (Describes (ap1 enum (natCode (progIx d))) (natCode d))
--     per day  d in [0..N] ) , together with the pigeonhole inequality
--     M < N .   This is EXTERNAL DATA : the surprise-exam predictions
--     and verifications in Kritchman-Raz form .   Per the handoff doc :
--     "the most honest move : just take DescFamConj as a (still
--     abstract) HYPOTHESIS in the concrete instantiation , since
--     DescFamConj's content is genuine external data" .
--
-- 2.  `BerryDataConj M enum`  --  the meta-pack
--       (kStar : Nat)
--       (kStarBound : NatLe kStar M)
--       (enumPin : Deriv (eqF (ap1 enum (natCode kStar))
--                              (enc (gLcodeDefConj M enum))))
--     encoding "the diagonal program  g_L  appears at index  kStar  in
--     the enumeration  enum " .   The handoff doc's Step 2-3 plan
--     (define  enumConcrete := compose1U parse (bitListAt Lstar)  and
--     compute  kStar  in Agda) requires fresh bit-list enumeration
--     machinery + a meta  termToNat  encoder that do NOT exist in
--     T4 ( grep confirmed :  no  bitListAt , no  kthProg , no
--     termToNat  anywhere ) .   The encoding-size machinery that DOES
--     exist  ( T4.ProgEnc.lenR_enc , T4.dLenStarDef ) proves SIZE
--     BOUNDS for the OLD diagonal shape  gLcodeDef Lstar ;  porting
--     those to the new  gLcodeDefConj M enum  shape is straightforward
--     but only addresses the size bound , NOT the enumeration pin .
--
--     Per the handoff doc itself :  "If  dLenStarDef  is itself a
--     residual ... STOP and report ( don't reinvent encoding-size
--     machinery here )" .   Although  dLenStarDef  IS shipped for the
--     OLD shape , the new  enumPin  is a STRICTLY HARDER artifact (it
--     requires a non-circular  enum  satisfying a meta-fixed-point :
--     gLcodeDefConj M enum  syntactically embeds  enum  via
--     predFlipDefConj M enum ,  so a closed  enum  satisfying
--     ap1 enum (natCode kStar) = enc (gLcodeDefConj M enum)
--     necessarily either implements a bit-list parser or is a Kleene
--     fixed point) .   Both routes are substantial new infrastructure
--     ( ~500-1000 LoC ) .   The honest move per the user's
--     "slow typecheck -> step back and abstract" principle :  ship the
--     wireup with BerryDataConj abstract , flag the encoding residual
--     for a future session that elects to either build the bit-list
--     enumerator or commit to the Kleene fixed point .
--
-- =====================================================================
-- IMPLEMENTATION NOTE.
-- =====================================================================
--
-- The body is a single composition :
--
--   surpriseG2ConjConcrete consts descFam bData conInt
--     = surpriseG2ConjFromDescFam consts descFam
--         (cgiConjBody (M consts) (enum consts) bData) conInt
--
-- Three of the four arguments are external hypotheses ;  the only
-- "computation" is closing the CGIConjSpec via cgiConjBody from the
-- BerryDataConj meta-pack .

module T4.SurpriseG2.SurpriseG2ConjConcrete where

open import T4.Base

open import T4.SurpriseG2.ConstantsConj
  using ( SurpriseConstsConj )
open import T4.SurpriseG2.CGIConjBody
  using ( BerryDataConj ; cgiConjBody )
open import T4.SurpriseG2.StageZeroNegsConj
  using ( DescFamConj )
open import T4.SurpriseG2.ConOpenIntDef
  using ( ConOpenInt )
open import T4.SurpriseG2.SurpriseG2Conj
  using ( surpriseG2ConjFromDescFam )

------------------------------------------------------------------------
-- The headline concrete wireup .
--
-- All four inputs are FIRST-CLASS DATA :
--   * consts  --  N , M , enum   (meta-Nat + Fun1 enumeration) .
--   * descFam --  per-day describes packs  +  M < N  pigeonhole seed .
--   * bData   --  (kStar , kStarBound , enumPin)  enumeration witness
--                  for the diagonal program  g_L = gLcodeDefConj M enum .
--   * conInt  --  T |- ~ (thmT(v0) = code(0=1))  open consistency .
--
-- No CGIConjSpec hypothesis remains :   cgiConjBody  builds it
-- internally from  bData  via the Berry-clash chain
-- ( T4.SurpriseG2.CGIConjBody ) .

surpriseG2ConjConcrete :
  (consts : SurpriseConstsConj) ->
  DescFamConj consts ->
  BerryDataConj (SurpriseConstsConj.M consts)
                (SurpriseConstsConj.enum consts) ->
  ConOpenInt ->
  Deriv (eqF O (ap1 s O))
surpriseG2ConjConcrete consts descFam bData conInt =
  let open SurpriseConstsConj consts using ( M ; enum )
  in surpriseG2ConjFromDescFam consts descFam
       (cgiConjBody M enum bData) conInt
