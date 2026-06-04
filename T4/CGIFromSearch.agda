{-# OPTIONS --without-K --exact-split #-}
{-# OPTIONS --safe #-}

-- T4.CGIFromSearch -- Chaitin-Goedel I assembled from the bounded search.
--
-- Ties T4.CompHitDef (the definable compressibility indicator) to
-- T4.CGINumRaw.cgi_inconsistent (the num-raw clash + Con).  The compressibility
-- fact  h : compHit z0 = 1  is now DERIVED from the bounded-search settling
-- (existsHitU_settles) at a witness  p0  whose program  Fst p0  is short and
-- describes  z0  -- i.e. the looping program g_L at its halt time, the
-- surprise.pdf "z has a short description / it is easy to run the program".
--
-- Remaining honest inputs (the run + the recogniser + Con):
--   * szFires  : szLeq (Fst p0) = 1            -- the program name fits L (dLen)
--   * evalFires: evalU(parse(Fst p0), Snd p0) = s z0   -- it outputs z0 (the run)
--   * predFires: evalU(parse(Fst p0), pred(Snd p0)) = O -- first at Snd p0
--   * fit      : leq p0 B                       -- the witness is in search range (FIT)
--   * dNeg     : thmT w0 = cNeg (codeFXeqY1 compHit z0 1)  -- the recogniser firing
--   * con      : ConSchema
-- None need codeFormula / isNat;  z0 = out_L w0  is a Term.

module T4.CGIFromSearch where

open import T4.Base
open import T4.Code          using ( falseF )
open import T4.ThmT          using ( thmT )
open import T4.DefWit        using ( cNeg )
open import T4.ConInj        using ( ConSchema )
open import T4.Thm12.Thm13   using ( codeFXeqY1 )
open import T4.CGINumRaw     using ( cgi_inconsistent )
open import T4.EvalUEval     using ( evalU )
open import T4.ProgParse     using ( parse )
import T4.CompHitDef

open import BRA3.ChurchLeq     using ( leq )
open import BRA3.Church        using ( predecessor )

------------------------------------------------------------------------
-- The assembly, parametric in the size indicator  szLeq  and the search-bound
-- function  constB (ap1 constB y = B) .

module Assemble
  (szLeq : Fun1)
  (szLeq_le_one : (c : Term) -> Deriv (leq (ap1 szLeq c) (ap1 s O)))
  (constB : Fun1) (B : Term)
  (constB_eq : (y : Term) -> Deriv (eqF (ap1 constB y) B))
  where

  open T4.CompHitDef.Rec szLeq szLeq_le_one
    using ( test_def_fires ; existsHitU ; existsHitU_settles
          ; compHitOf ; compHitOf_eq )

  -- the concrete compressibility indicator.
  compHit : Fun1
  compHit = compHitOf constB

  ----------------------------------------------------------------------
  -- CGI from the search: the witness  p0  (a short program describing z0,
  -- in range) + the recogniser firing dNeg + Con  ==>  falseF .

  cgi_from_search :
    Deriv ConSchema ->
    (z0 w0 p0 : Term) -> Closed z0 -> Closed B -> Closed p0 ->
    Deriv (leq p0 B) ->                                                          -- FIT
    Deriv (eqF (ap1 szLeq (ap1 Fst p0)) (ap1 s O)) ->                            -- |Fst p0| <= L
    Deriv (eqF (ap2 evalU (ap1 parse (ap1 Fst p0)) (ap1 Snd p0)) (ap1 s z0)) ->  -- outputs z0
    Deriv (eqF (ap2 evalU (ap1 parse (ap1 Fst p0)) (ap1 predecessor (ap1 Snd p0))) O) -> -- 0 at n-1
    Deriv (eqF (ap1 thmT w0) (cNeg (codeFXeqY1 compHit z0 (ap1 s O)))) ->        -- dNeg
    Deriv falseF
  cgi_from_search con z0 w0 p0 clZ0 clB clP0 fit szFires evalFires predFires dNeg =
    let exHit : Deriv (eqF (existsHitU z0 B) (ap1 s O))
        exHit = mp (existsHitU_settles z0 B p0 clZ0 clB clP0
                      (test_def_fires z0 p0 szFires evalFires predFires)) fit
        h : Deriv (eqF (ap1 compHit z0) (ap1 s O))
        h = ruleTrans (compHitOf_eq constB B constB_eq z0) exHit
    in cgi_inconsistent con compHit z0 w0 h dNeg
