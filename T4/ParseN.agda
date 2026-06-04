{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ParseN -- brick 2 of the number-code Chaitin redo
-- (CHAITIN-NUMBER-CODE-HANDOFF.md S2 / S6.2).
--
-- Programs ARE numbers.  The decoder reads a number  x  AS its base-3 digit
-- string ( candidate x ) and then tree-parses it:
--
--   parseN   := compose1U parse candidate          ( parseN x = parse (candidate x) )
--   runProgN := Fan (Lift1 parseN) v evalU          ( runProgN x y = evalU (parseN x) y )
--   defN x z y := eqF (ap2 runProgN x y) (ap1 s z)  ( "number x, run y steps, outputs z" )
--
-- The DIAGONAL membership ( surjective-pairing-free ) :  for any tree  gL  ,
-- with  n0 = rank (treeToDigits gL) ,
--
--   candidate (natCode n0) = enc gL                 ( candidate_at_diag )
--   parseN  (natCode n0)   = gL                      ( parseN_at_diag , needs InAlph gL )
--   runProgN (natCode n0) y = evalU gL y             ( runProgN_at_diag )
--
-- every step a proved equation -- NO Cantor identity  natCode(codeNumber t)=t .

module T4.ParseN where

open import T4.Base
open import T4.ProgParse using ( parse ; parse_enc ; InAlph )
open import T4.ProgEnc   using ( enc )
open import T4.EvalUEval using ( evalU )
open import T4.Candidate using ( candidate )
open import T4.CandidateCover using ( TStr ; rank ; toStr ; coverage )
open import T4.TreeToDigits using ( treeToDigits ; toStr_treeToDigits )

open import BRA3.PairAlgebra using ( Fan ; Lift1 ; axFan ; axLift ; compose1U ; compose1U_eq )

------------------------------------------------------------------------
-- SECTION 1.  parseN := parse . candidate .

parseN : Fun1
parseN = compose1U parse candidate

parseN_eq :
  (x : Term) -> Deriv (eqF (ap1 parseN x) (ap1 parse (ap1 candidate x)))
parseN_eq x = compose1U_eq parse candidate x

------------------------------------------------------------------------
-- SECTION 2.  runProgN := the universal machine on a program NUMBER.
--   ap2 runProgN x y = evalU (parseN x) y   ( mirrors T4.Kdef.runProg ).

-- SEALED ( abstract ) so  codeFun2 runProgN  stays NEUTRAL : it embeds the huge
--  Fan / Lift1 / parseN ( parse + candidate ) / evalU  code, renormalised across
-- the clash's many  cAp2f runProgN  occurrences ( >20s ).  The run law lives in
-- the block ( it unfolds runProgN );  downstream uses only the law + opaque code.
abstract
  runProgN : Fun2
  runProgN = Fan (Lift1 parseN) v evalU

  runProgN_eq :
    (x y : Term) ->
    Deriv (eqF (ap2 runProgN x y) (ap2 evalU (ap1 parseN x) y))
  runProgN_eq x y =
    ruleTrans (axFan (Lift1 parseN) v evalU x y)
      (ruleTrans (congL evalU (ap2 v x y) (axLift parseN x y))
                 (congR evalU (ap1 parseN x) (ax_v x y)))

------------------------------------------------------------------------
-- SECTION 3.  The definability matrix.

defN : Term -> Term -> Term -> Formula
defN x z y = eqF (ap2 runProgN x y) (ap1 s z)

------------------------------------------------------------------------
-- SECTION 4.  The diagonal membership.   n0 := rank (treeToDigits gL) .

diagRank : Term -> Nat
diagRank gL = rank (treeToDigits gL)

-- candidate (natCode n0) = enc gL    ( coverage + the digit-extractor law ).
candidate_at_diag :
  (gL : Term) ->
  Deriv (eqF (ap1 candidate (natCode (diagRank gL))) (enc gL))
candidate_at_diag gL =
  eqSubst (\ t -> Deriv (eqF (ap1 candidate (natCode (rank (treeToDigits gL)))) t))
          (toStr_treeToDigits gL)
          (coverage (treeToDigits gL))

-- parseN (natCode n0) = gL    ( + parse_enc , needs  InAlph gL ).
parseN_at_diag :
  (gL : Term) -> InAlph gL ->
  Deriv (eqF (ap1 parseN (natCode (diagRank gL))) gL)
parseN_at_diag gL ia =
  ruleTrans (parseN_eq (natCode (diagRank gL)))
    (ruleTrans (cong1 parse (candidate_at_diag gL))
               (parse_enc gL ia))

-- runProgN (natCode n0) y = evalU gL y    ( decoder-agnostic run ).
runProgN_at_diag :
  (gL : Term) -> InAlph gL -> (y : Term) ->
  Deriv (eqF (ap2 runProgN (natCode (diagRank gL)) y) (ap2 evalU gL y))
runProgN_at_diag gL ia y =
  ruleTrans (runProgN_eq (natCode (diagRank gL)) y)
            (congL evalU y (parseN_at_diag gL ia))
