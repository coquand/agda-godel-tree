{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinNumGI -- brick 5 (the GI clash) of the number-code Chaitin redo,
-- the SIMPLEST route for GI alone (CHAITIN-NUMBER-CODE-HANDOFF.md S5.0).
--
-- Programs ARE numbers; the finite candidate set { |p| <= n } is the initial
-- segment { p < N }, N = 3^{n+1} symbolic, predN := N-1.  K(r)>n is kept as the
-- OPEN formula ( free p = var 0 , fuel y = var 1 ), guard the clean O(1)  p < N :
--
--   Kgt  =  imp (leq (var 0) predN) (neg (defN (var 0) r (var 1)))
--        =  ( p <= predN )  ->  ~ ( runProgN p y = s r )
--
-- ( leq a b = sub a b = O , i.e. a <= b ).  This is honest and  internalCover-
-- free precisely because we DEFINE K(r)>n this way (T proves it as a black box);
-- there is no conjunction->open bridge to build.  The clash is pure SUBSTITUTION
-- (BRA Rule III) of the diagonal  p := n0 , y := y0 , then the  n0 < N  size pin
-- discharges the guard and the diagonal's run  defN n0 r y0  refutes the
-- negation -- ExFalso delivers  0 = 1 .  No coverage, no surjective pairing.
--
-- All three premises are HONEST, UNDISCHARGED hypotheses ( the reflection that
-- supplies  T |- Kgt  for the actual diagonal is the encoded layer, separate ) :
--   * hyp  : Deriv Kgt                       -- T proves K(r)>n
--   * pin  : Deriv (leq n0 predN)            -- |gL| <= n , i.e. n0 < N
--   * run  : Deriv (defN n0 r y0)            -- the diagonal runs, outputs r
-- giClashDiag specialises  n0 := natCode (diagRank gL)  and builds  run  from the
-- decoder-agnostic  runProgN (natCode n0) y = evalU gL y  ( T4.ParseN ) plus the
-- diagonal's genuine evalU run.

open import T4.Base

module T4.ChaitinNumGI
  (predN r : Term)
  (predN_c0 : (a : Term) -> Eq (substT zero a predN) predN)
  (predN_c1 : (a : Term) -> Eq (substT (suc zero) a predN) predN)
  (r_c0 : (a : Term) -> Eq (substT zero a r) r)
  (r_c1 : (a : Term) -> Eq (substT (suc zero) a r) r)
  where

open import T4.ParseN using ( runProgN ; defN ; diagRank ; runProgN_at_diag )
open import T4.ExFalso using ( exFalso )
open import T4.ProgParse using ( InAlph )
open import T4.EvalUEval using ( evalU )

open import BRA3.Numerals  using ( substT_natCode )
open import BRA3.Church    using ( sub )
open import BRA3.ChurchLeq using ( leq )
open import BRA3.Formula   using ( neg ; imp )

------------------------------------------------------------------------
-- SECTION 1.  The open K-formula  K(r)>n .   free  var 0 = p ,  var 1 = y .

Kgt : Formula
Kgt = imp (leq (var zero) predN) (neg (defN (var zero) r (var (suc zero))))

-- 0 = 1 , the inconsistency target ( = codeFalse's inner formula ).
falseEq : Formula
falseEq = eqF O (ap1 s O)

------------------------------------------------------------------------
-- SECTION 2.  The substitution clash, generic in the diagonal number  n0 .

module _ (n0 y0 : Term)
         (n0_c1 : (a : Term) -> Eq (substT (suc zero) a n0) n0)
  where

  -- the clean doubly-substituted instance  Kgt[ p := n0 , y := y0 ] .
  KgtInst : Formula
  KgtInst = imp (leq n0 predN) (neg (defN n0 r y0))

  -- substF (suc zero) y0 (substF zero n0 Kgt)  reduces definitionally to
  -- mk (substT 1 y0 n0) (substT 1 y0 (substT 0 n0 predN)) (substT 1 y0 (substT 0 n0 r)) ,
  -- cleaned to KgtInst = mk n0 predN r by the three closedness witnesses.
  private
    mk : Term -> Term -> Term -> Formula
    mk N X Y = imp (eqF (ap2 sub N X) O)
                   (neg (eqF (ap2 runProgN N y0) (ap1 s Y)))

    nEq : Eq (substT (suc zero) y0 n0) n0
    nEq = n0_c1 y0

    predEq : Eq (substT (suc zero) y0 (substT zero n0 predN)) predN
    predEq = eqTrans (eqCong (substT (suc zero) y0) (predN_c0 n0)) (predN_c1 y0)

    rEq : Eq (substT (suc zero) y0 (substT zero n0 r)) r
    rEq = eqTrans (eqCong (substT (suc zero) y0) (r_c0 n0)) (r_c1 y0)

    subst_eq :
      Eq (substF (suc zero) y0 (substF zero n0 Kgt)) KgtInst
    subst_eq =
      eqTrans (eqCong (\ N -> mk N (substT (suc zero) y0 (substT zero n0 predN))
                                   (substT (suc zero) y0 (substT zero n0 r))) nEq)
      (eqTrans (eqCong (\ X -> mk n0 X (substT (suc zero) y0 (substT zero n0 r))) predEq)
               (eqCong (\ Y -> mk n0 predN Y) rEq))

  giClash :
    Deriv Kgt ->                       -- T |- K(r)>n  ( the reflected theorem )
    Deriv (leq n0 predN) ->            -- n0 < N : the honest size pin
    Deriv (defN n0 r y0) ->            -- the diagonal runs, outputs r
    Deriv falseEq
  giClash hyp pin run =
    let d2 : Deriv (substF (suc zero) y0 (substF zero n0 Kgt))
        d2 = ruleInst (suc zero) y0 (ruleInst zero n0 hyp)
        dInst : Deriv KgtInst
        dInst = eqSubst (\ F -> Deriv F) subst_eq d2
        negDef : Deriv (neg (defN n0 r y0))
        negDef = mp dInst pin
    in exFalso (defN n0 r y0) falseEq run negDef

------------------------------------------------------------------------
-- SECTION 3.  Specialisation to the actual NUMBER-diagonal.
--   n0 := natCode (diagRank gL) , and the run is built from the
--   decoder-agnostic  runProgN (natCode n0) y0 = evalU gL y0  plus the
--   diagonal's genuine evalU run  ( a provable Sigma_1 fact ).

giClashDiag :
  (gL : Term) -> InAlph gL -> (y0 : Term) ->
  Deriv Kgt ->
  Deriv (leq (natCode (diagRank gL)) predN) ->
  Deriv (eqF (ap2 evalU gL y0) (ap1 s r)) ->      -- the diagonal outputs r at y0
  Deriv falseEq
giClashDiag gL ia y0 hyp pin evalRun =
  let n0 : Term
      n0 = natCode (diagRank gL)
      run : Deriv (defN n0 r y0)
      run = ruleTrans (runProgN_at_diag gL ia y0) evalRun
  in giClash n0 y0 (\ a -> substT_natCode (suc zero) a (diagRank gL)) hyp pin run
