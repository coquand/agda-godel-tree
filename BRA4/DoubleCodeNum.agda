{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.DoubleCodeNum -- the object realisation of  codeTerm . codeTerm  on
-- NUMERALS (CHAITIN-G1-SEARCH-DESIGN.md, the "codeTermF" obstacle).
--
-- The design note named a general object coding functor  codeTermF : Fun1
-- (codeTermF c = codeTerm c) as the obstacle behind the bridge's DOUBLE-CODING
-- (the subject sits at  codeTerm (codeTerm x)  in  codeFormula (neg (atomForm
-- ell x)) , confirmed in ChaitinCodeShape.agda).  A GENERAL codeTermF would be
-- a binary tree fold (Fst-recursion, the FoldRec-hard case).
--
-- BUT the Chaitin search's subject is always a NUMBER (the machine output), so
-- the only thing actually needed is  codeTerm (codeTerm (numeral))  as a
-- function of the numeral -- and THAT is PRIMITIVE-RECURSIVE in the numeral
-- (no tree fold): each successor wraps the previous value in a FIXED context,
-- because  codeTerm (natCode (suc m)) = Pair (natCode tag_ap1) (Pair (codeFun1
-- s) (codeTerm (natCode m)))  is right-recursive.  So  doubleCodeNum  is a plain
-- BRA  R -recursion on the numeral.  This is the construction PUSHING BACK on
-- the interface (validate-by-construction): the obstacle simplifies once the
-- numeral restriction is taken into account.
--
--   doubleCodeNum O      = O
--   doubleCodeNum (s m)  = stepContext (doubleCodeNum m)
--   doubleCodeNum_correct :  doubleCodeNum (natCode n) = codeTerm (codeTerm (natCode n))

module BRA4.DoubleCodeNum where

open import BRA4.Base
open import BRA4.Tags using ( tag_ap1 ; tag_ap2 ; tag_s ; tag_o ; tag_u ; tag_C
                            ; tag_v ; tag_R )
open import BRA4.Code using ( codeTerm ; codeFun1 ; codeFun2 )
open import BRA4.Thm12.ConstTermFun1
  using ( NoVar ; NoVarAnd ; mkAnd ; NoVar_natCode
        ; constTermFun1 ; constTermFun1_eq )

------------------------------------------------------------------------
-- SECTION 1.  NoVar for code constants (local; mirrors codeFun structure).

NoVar_codeFun1L : (f : Fun1) -> NoVar (codeFun1 f)
NoVar_codeFun2L : (g : Fun2) -> NoVar (codeFun2 g)
NoVar_codeFun1L s          = NoVar_natCode tag_s
NoVar_codeFun1L o          = NoVar_natCode tag_o
NoVar_codeFun1L u          = NoVar_natCode tag_u
NoVar_codeFun1L (C g h1 h2) =
  mkAnd (NoVar_natCode tag_C)
    (mkAnd (NoVar_codeFun2L g)
      (mkAnd (NoVar_codeFun1L h1) (NoVar_codeFun1L h2)))
NoVar_codeFun2L v          = NoVar_natCode tag_v
NoVar_codeFun2L (R g h1 h2) =
  mkAnd (NoVar_natCode tag_R)
    (mkAnd (NoVar_codeFun1L g)
      (mkAnd (NoVar_codeFun2L h1) (NoVar_codeFun2L h2)))

-- NoVar of the code of a numeral.
NoVar_codeTermNat : (k : Nat) -> NoVar (codeTerm (natCode k))
NoVar_codeTermNat zero    = tt
NoVar_codeTermNat (suc j) =
  mkAnd (NoVar_natCode tag_ap1)
    (mkAnd (NoVar_natCode tag_s) (NoVar_codeTermNat j))

------------------------------------------------------------------------
-- SECTION 2.  The fixed step context  stepContext r .
--
-- codeTerm (codeTerm (natCode (suc m)))  unfolds DEFINITIONALLY to
--   stepContext (codeTerm (codeTerm (natCode m)))
-- (codeTerm reduces on the  ap1 s / ap2 Pair  constructors).  Constants:
--   e3 = natCode tag_ap2 , cP = codeFun2 Pair ,
--   k2 = codeTerm (natCode tag_ap1) , k4 = codeTerm (natCode tag_s) .

e3c : Term
e3c = natCode tag_ap2

cPc : Term
cPc = codeFun2 Pair

k2c : Term
k2c = codeTerm (natCode tag_ap1)

k4c : Term
k4c = codeTerm (natCode tag_s)

stepContext : Term -> Term
stepContext r =
  ap2 Pair e3c
    (ap2 Pair cPc
      (ap2 Pair k2c
        (ap2 Pair e3c
          (ap2 Pair cPc
            (ap2 Pair k4c r)))))

stepContext_cong :
  {r r' : Term} -> Deriv (eqF r r') ->
  Deriv (eqF (stepContext r) (stepContext r'))
stepContext_cong e =
  congR Pair e3c
    (congR Pair cPc
      (congR Pair k2c
        (congR Pair e3c
          (congR Pair cPc
            (congR Pair k4c e)))))

------------------------------------------------------------------------
-- SECTION 3.  The step functor  stepDC : Fun2  realising  stepContext .
--
-- pairConst c inner = Fan (Lift1 (constTermFun1 c)) inner Pair :  applied to
-- (pkg, prev) it gives  Pair c (inner pkg prev) .  Nest six of them (innermost
-- inner = v , the accumulator projection) to build  stepContext prev .

pairConst : Term -> Fun2 -> Fun2
pairConst c inner = Fan (Lift1 (constTermFun1 c)) inner Pair

pairConst_eq :
  (c : Term) -> NoVar c -> (inner : Fun2) (pkg prev : Term) ->
  Deriv (eqF (ap2 (pairConst c inner) pkg prev)
             (ap2 Pair c (ap2 inner pkg prev)))
pairConst_eq c nv inner pkg prev =
  let e1 : Deriv (eqF (ap2 (pairConst c inner) pkg prev)
                      (ap2 Pair (ap2 (Lift1 (constTermFun1 c)) pkg prev)
                                (ap2 inner pkg prev)))
      e1 = axFan (Lift1 (constTermFun1 c)) inner Pair pkg prev
      eleft : Deriv (eqF (ap2 (Lift1 (constTermFun1 c)) pkg prev) c)
      eleft = ruleTrans (axLift (constTermFun1 c) pkg prev)
                        (constTermFun1_eq c nv pkg)
  in ruleTrans e1 (congL Pair (ap2 inner pkg prev) eleft)

stepDC : Fun2
stepDC =
  pairConst e3c
    (pairConst cPc
      (pairConst k2c
        (pairConst e3c
          (pairConst cPc
            (pairConst k4c v)))))

stepDC_eq :
  (pkg prev : Term) ->
  Deriv (eqF (ap2 stepDC pkg prev) (stepContext prev))
stepDC_eq pkg prev =
  ruleTrans (pairConst_eq e3c (NoVar_natCode tag_ap2) _ pkg prev)
    (congR Pair e3c
      (ruleTrans (pairConst_eq cPc (NoVar_codeFun2L Pair) _ pkg prev)
        (congR Pair cPc
          (ruleTrans (pairConst_eq k2c (NoVar_codeTermNat tag_ap1) _ pkg prev)
            (congR Pair k2c
              (ruleTrans (pairConst_eq e3c (NoVar_natCode tag_ap2) _ pkg prev)
                (congR Pair e3c
                  (ruleTrans (pairConst_eq cPc (NoVar_codeFun2L Pair) _ pkg prev)
                    (congR Pair cPc
                      (ruleTrans (pairConst_eq k4c (NoVar_codeTermNat tag_s) v pkg prev)
                        (congR Pair k4c (ax_v pkg prev))))))))))))

------------------------------------------------------------------------
-- SECTION 4.  doubleCodeNum : Fun1  via  R  on the numeral (spec O fixed).

dcRec : Fun2
dcRec = R o stepDC Pair

doubleCodeNum : Fun1
doubleCodeNum = C dcRec o u

doubleCodeNum_unfold :
  (t : Term) -> Deriv (eqF (ap1 doubleCodeNum t) (ap2 dcRec O t))
doubleCodeNum_unfold t =
  ruleTrans (ax_C dcRec o u t)
    (ruleTrans (congL dcRec (ap1 u t) (ax_o t))
               (congR dcRec O (ax_u t)))

doubleCodeNum_at_O : Deriv (eqF (ap1 doubleCodeNum O) O)
doubleCodeNum_at_O =
  ruleTrans (doubleCodeNum_unfold O)
    (ruleTrans (ax_R_base o stepDC Pair O) (ax_o O))

doubleCodeNum_at_succ :
  (t : Term) ->
  Deriv (eqF (ap1 doubleCodeNum (ap1 s t))
             (stepContext (ap1 doubleCodeNum t)))
doubleCodeNum_at_succ t =
  let e1 : Deriv (eqF (ap1 doubleCodeNum (ap1 s t)) (ap2 dcRec O (ap1 s t)))
      e1 = doubleCodeNum_unfold (ap1 s t)
      e2 : Deriv (eqF (ap2 dcRec O (ap1 s t))
                      (ap2 stepDC (ap2 Pair O t) (ap2 dcRec O t)))
      e2 = ax_R_step o stepDC Pair O t
      e3 : Deriv (eqF (ap2 stepDC (ap2 Pair O t) (ap2 dcRec O t))
                      (stepContext (ap2 dcRec O t)))
      e3 = stepDC_eq (ap2 Pair O t) (ap2 dcRec O t)
      e4 : Deriv (eqF (stepContext (ap2 dcRec O t))
                      (stepContext (ap1 doubleCodeNum t)))
      e4 = stepContext_cong (ruleSym (doubleCodeNum_unfold t))
  in ruleTrans e1 (ruleTrans e2 (ruleTrans e3 e4))

------------------------------------------------------------------------
-- SECTION 5.  Correctness:  doubleCodeNum (natCode n) = codeTerm (codeTerm
-- (natCode n)) .  Meta-induction on n; the step's definitional equality
-- codeTerm (codeTerm (natCode (suc m))) = stepContext (codeTerm (codeTerm
-- (natCode m)))  is exactly how  stepContext  was chosen.

doubleCodeNum_correct :
  (n : Nat) ->
  Deriv (eqF (ap1 doubleCodeNum (natCode n))
             (codeTerm (codeTerm (natCode n))))
doubleCodeNum_correct zero    = doubleCodeNum_at_O
doubleCodeNum_correct (suc m) =
  ruleTrans (doubleCodeNum_at_succ (natCode m))
            (stepContext_cong (doubleCodeNum_correct m))
