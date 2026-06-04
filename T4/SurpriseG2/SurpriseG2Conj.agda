{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.SurpriseG2Conj -- the headline theorem of the
-- conjunction-shape  KdefConj  reformulation per
-- T4/NEXT-SESSION-KDEFCONJ.md .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- `surpriseG2Conj`  --  the surprise-G2 theorem at the new K-formula
-- shape :
--
--   (consts : SurpriseConstsConj) ->
--   PerProgramNegConj consts (natCode zero) ->     -- day-0 per-prog negs
--   CGIConjSpec thmT (KcodeConj (M consts) (enum consts)) ->
--   ConOpenInt ->                                   -- T |- ~ (thmT(v0) = code(0=1))
--   Deriv (eqF O (ap1 s O))                         -- T |- 0 = 1
--
-- Body: same four-line composition as the OLD  surpriseG2 (T4/SurpriseG2.agda),
-- routed through the new types :
--
--   kdefFromNegsConj            (the new K-formula assembly)
--      |
--      v
--   sigma1KdefConj_KcodeShape    (Sigma1-internalisation)
--      |
--      v
--   CGIConjSpec.cgiConj          (Berry clash)
--      |
--      v   (with ConOpenInt + axExFalso)
--   Deriv (eqF O (ap1 s O))
--
-- =====================================================================
-- WHAT IS DEFERRED.
-- =====================================================================
--
-- * Concrete  `CGIConjSpec`  body (the Berry-chain proof at the new shape) .
--   The ONLY mathematical claim the framework requires that the
--   framework cannot self-derive .
--
-- * `DescFamConj` -> `PerProgramNegConj` bridge (parallel to the OLD
--   stageZeroNegs ) .   For this minimal wireup, the day-0 per-prog negs
--   are taken DIRECTLY as a parameter ; the meta-pigeonhole-from-DescFam
--   layer is a follow-up.

module T4.SurpriseG2.SurpriseG2Conj where

open import T4.Base
open import T4.ThmT                          using ( thmT )
open import T4.Code                          using ( codeFalse )
open import BRA3.Contrapositive                using ( axExFalso )

open import T4.SurpriseG2.ConstantsConj      using ( SurpriseConstsConj )
open import T4.SurpriseG2.KdefConj           using ( KdefConj )
open import T4.SurpriseG2.KFormulaFromNegsConj
  using ( PerProgramNegConj ; kdefFromNegsConj )
open import T4.SurpriseG2.KcodeConj          using ( KcodeConj )
open import T4.SurpriseG2.Sigma1KdefConj     using ( sigma1KdefConj_KcodeShape )
open import T4.SurpriseG2.CGIConjSpec        using ( CGIConjSpec )
open import T4.SurpriseG2.ConOpenIntDef      using ( ConOpenInt )
open import T4.SurpriseG2.StageZeroNegsConj
  using ( DescFamConj ; descFamToNegs0 )

import T4.SurpriseG2.CGIConjSpec as CGIS

-- Both  sigma1KdefConj_KcodeShape  and  CGIConjSpec  use the SAME
-- Sigma  ( T4.SurpriseG2.CGIConjSpec.Sigma )  now -- the previous
-- separation via  T4.ChaitinG1CoreNumRaw.Sigma  has been retired :
-- importing  ChaitinG1CoreNumRaw  transitively pulls in  T4.CgiClash
-- whose  SomeProof  record has the dependent thmT-elaboration issue
-- ( see  CgiClashConj.agda  header ) ,  pushing this file's typecheck
-- above 20s .   With the single-Sigma  CGIS import , typecheck is < 2s .

------------------------------------------------------------------------
-- The headline theorem.
--
-- (consts : SurpriseConstsConj)
--    M  + enum  =  meta-Nat + Fun1 enumeration of M+1 short programs .
-- (negs0 : PerProgramNegConj consts (natCode zero))
--    For each  k <= M ,  Deriv (~definable (ap1 enum (natCode k))
--    (natCode 0) (var 1)) .   I.e., no enumerated short program describes
--    day 0 .   ( In the surprise-G2 sketch this comes from pigeonhole
--    on the  M+1  describing programs supplied by DescFam : two days
--    share a short program, both describe their respective days, giving
--    0=1 ; ex-falso to any per-program neg . )
-- (cgiSpec : CGIConjSpec thmT (KcodeConj M enum))
--    The Berry-clash function at the new K-formula shape .
-- (conInt : ConOpenInt)
--    T |- ~ (thmT(v0) = code(0=1)) , the open consistency hypothesis .

surpriseG2Conj :
  (consts : SurpriseConstsConj) ->
  PerProgramNegConj consts (natCode zero) ->
  CGIConjSpec thmT (KcodeConj (SurpriseConstsConj.M consts)
                              (SurpriseConstsConj.enum consts)) ->
  ConOpenInt ->
  Deriv (eqF O (ap1 s O))
surpriseG2Conj consts negs0 cgiSpec conInt =
  let open SurpriseConstsConj consts using ( M ; enum )

      -- Step 1 : assemble the K-formula at  subject := natCode zero
      -- from the M+1 per-program negs ( = `kdefFromNegsConj` ) .
      dKdef : Deriv (KdefConj M enum (natCode zero))
      dKdef = kdefFromNegsConj consts (natCode zero) negs0

      -- Step 2 : Sigma_1 -internalise to a closed thmT-fact at the
      -- KcodeConj  shape ( = `sigma1KdefConj_KcodeShape` ) .
      thmFact :
        CGIS.Sigma Term (\ w ->
          Deriv (eqF (ap1 thmT w)
                      (ap1 (KcodeConj M enum) (natCode zero))))
      thmFact = sigma1KdefConj_KcodeShape M enum zero dKdef

      w0 : Term
      w0 = CGIS.Sigma.fst thmFact

      dThm0 :
        Deriv (eqF (ap1 thmT w0)
                    (ap1 (KcodeConj M enum) (natCode zero)))
      dThm0 = CGIS.Sigma.snd thmFact

      -- Step 3 : apply  CGIConjSpec.cgiConj  to get a thmT-fact at
      -- codeFalse .   This is the Berry clash at the new shape .
      cgiOut :
        CGIS.Sigma Term (\ z ->
          Deriv (eqF (ap1 thmT z) codeFalse))
      cgiOut = CGIConjSpec.cgiConj cgiSpec w0 (natCode zero) dThm0

      z : Term
      z = CGIS.Sigma.fst cgiOut

      dFalse_z : Deriv (eqF (ap1 thmT z) codeFalse)
      dFalse_z = CGIS.Sigma.snd cgiOut

      -- Step 4 : close out via  ConOpenInt + axExFalso , exactly as
      -- in  step_from_thm_fact  ( T4.SurpriseG2.Step ) .
      P_inc : Formula
      P_inc = eqF (ap1 thmT z) codeFalse

      hypAtZ : Deriv (neg P_inc)
      hypAtZ = inst_collapse z (ruleInst zero z conInt)

      Q : Formula
      Q = eqF O (ap1 s O)
  in mp (mp (axExFalso P_inc Q) dFalse_z) hypAtZ
  where
    -- Helper :   substF zero z (neg (eqF (ap1 thmT (var zero)) codeFalse))
    -- reduces DEFINITIONALLY to   neg (eqF (ap1 thmT z) codeFalse) , since
    --   - `neg P = imp P falseF` , and falseF = eqF O (sO) , NoVar at 0 ;
    --   - `eqF (ap1 thmT (var zero)) codeFalse` substitutes var 0 -> z
    --     to give `eqF (ap1 thmT z) (substT zero z codeFalse)` ;
    --   - `codeFalse` is a closed natCode , so  substT zero z codeFalse =
    --     codeFalse  ( definitionally for natCode-shaped terms ) .
    -- The identity holds definitionally ; this helper is just a witness
    -- to that fact mirroring  step_from_thm_fact.inst_collapse .
    inst_collapse :
      (z : Term) ->
      Deriv (substF zero z (neg (eqF (ap1 thmT (var zero)) codeFalse))) ->
      Deriv (neg (eqF (ap1 thmT z) codeFalse))
    inst_collapse z d = d

------------------------------------------------------------------------
-- Convenience wrapper :  surpriseG2ConjFromDescFam .
--
-- The day-0 per-prog negs are NOT taken as a parameter ; instead they
-- are produced from a  DescFamConj  via the meta-pigeonhole bridge
-- T4.SurpriseG2.StageZeroNegsConj.descFamToNegs0 .
--
--   (consts : SurpriseConstsConj)
--   (descFam : DescFamConj consts)              -- the per-day describes
--                                                  packs + bound + pigeonhole
--                                                  inequality (M < N)
--   (cgiSpec : CGIConjSpec thmT (KcodeConj M enum))
--   (conInt  : ConOpenInt)
--   ----------------------------------------------------------------
--   Deriv (eqF O (ap1 s O))                      -- T |- 0 = 1

surpriseG2ConjFromDescFam :
  (consts : SurpriseConstsConj) ->
  DescFamConj consts ->
  CGIConjSpec thmT (KcodeConj (SurpriseConstsConj.M consts)
                              (SurpriseConstsConj.enum consts)) ->
  ConOpenInt ->
  Deriv (eqF O (ap1 s O))
surpriseG2ConjFromDescFam consts descFam cgiSpec conInt =
  surpriseG2Conj consts (descFamToNegs0 consts descFam) cgiSpec conInt
