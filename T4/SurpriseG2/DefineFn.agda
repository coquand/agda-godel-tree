{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.SurpriseG2.DefineFn --
--
-- The INTERNAL FUNCTION `define` corresponding to clos's `describe(p, l, r)` :
--
--   define(p, l, r)  =  s O   iff   runProg p l = s r
--                       O      otherwise
--
-- I.e., a DECIDABLE Fun2 computing the describe-predicate as a 0/1 value .
-- The describe-FORMULA becomes the closed equation
--
--   `eqF (ap2 define (ap2 Pair p l) r) (ap1 s O)`
--
-- whose Sigma_1 internalisation via  thm12_Fun2 define  gives the encoded
-- chain its closed thmT-fact directly , bypassing the need for external
-- runs Derivs ( see T4/clos lines 27-46 and the user's clarification
-- that completeness of internal evaluation + thm12 on the describe
-- function discharges the antecedent at the thmT level ) .
--
-- =====================================================================
-- WHAT THIS FILE SHIPS.
-- =====================================================================
--
-- * `define : Fun2`
--     The GENERAL describe-as-function : applied to  (Pair p l)  and  r ,
--     returns  natEqF (runProg p l) (s r)  ( = s O if equal , O else ) .
--     Construction :
--        Fan (Fan (Lift1 Fst) (Lift1 Snd) runProg) (Lift2 s) natEqF .
--
-- * `define_eq : (q r : Term) ->
--      Deriv (eqF (ap2 define q r)
--                  (ap2 natEqF (ap2 runProg (ap1 Fst q) (ap1 Snd q)) (ap1 s r)))`
--     The closed-form equation , uniform in  q .
--
-- * `define_at_Pair_eq : (p l r : Term) ->
--      Deriv (eqF (ap2 define (ap2 Pair p l) r)
--                  (ap2 natEqF (ap2 runProg p l) (ap1 s r)))`
--     At  q := Pair p l : reduces  Fst (Pair p l) -> p ,  Snd (Pair p l) -> l
--     via  axFst / axSnd .   This is the form the framework consumes .
--
-- * `define_p : Term -> Fun2`
--     The PER-PROGRAM family : for each closed program  p , a closed Fun2
--     taking  (l, r) , returning  natEqF (runProg p l) (s r) .   Construction :
--        Fan (Fan (Lift1 (constTermFun1 p)) (Lift1 u) runProg) (Lift2 s) natEqF .
--
-- * `define_p_eq : (p : Term) -> NoVar p -> (l r : Term) ->
--      Deriv (eqF (ap2 (define_p p) l r) (ap2 natEqF (ap2 runProg p l) (ap1 s r)))`
--     The per-program equation , requiring  NoVar p  ( so  constTermFun1 p
--     collapses ) .
--
-- =====================================================================
-- DOWNSTREAM USE.
-- =====================================================================
--
-- The framework will consume ONLY  define_p  ( one per enumerated short
-- program ) :  the K-formula  KdefBigConj  's per-program negs become
--   `neg (eqF (ap2 (define_p (ap1 enum (natCode k))) (var zero) subject) (ap1 s O))`
-- which  thm12_Fun2 (define_p (ap1 enum (natCode k)))  internalises as
-- a closed thmT-fact ; the encoded_mp chain then discharges the antecedent
-- BigConj_rest at the thmT level uniformly in the per-day  (k_d, l_d, d) .
--
-- The general  define  is shipped for completeness / future use ( e.g.,
-- if a single thm12 application across all programs is preferred ) .

module T4.SurpriseG2.DefineFn where

open import T4.Base
open import BRA3.Fan              using ( Fan ; Lift1 ; Lift2 ; Fan_eq ; Lift1_eq
                                        ; Lift2_eq )
open import BRA3.ChurchT117       using ( Fst )
open import BRA3.ChurchT116       using ( Snd )
open import BRA3.PairAlgebra      using ( axFst ; axSnd )
open import BRA3.SubT.NatEq       using ( natEqF )
open import T4.Kdef             using ( runProg )
open import T4.Thm12.ConstTermFun1
  using ( constTermFun1 ; constTermFun1_eq ; NoVar )

------------------------------------------------------------------------
-- The GENERAL define : takes  (Pair p l)  and  r .

define : Fun2
define = Fan (Fan (Lift1 Fst) (Lift1 Snd) runProg) (Lift2 s) natEqF

------------------------------------------------------------------------
-- The general equation : ap2 define q r reduces step-by-step .

define_eq :
  (q r : Term) ->
  Deriv (eqF (ap2 define q r)
              (ap2 natEqF (ap2 runProg (ap1 Fst q) (ap1 Snd q)) (ap1 s r)))
define_eq q r =
  let inner_fan : Fun2
      inner_fan = Fan (Lift1 Fst) (Lift1 Snd) runProg

      step_outer :
        Deriv (eqF (ap2 define q r)
                    (ap2 natEqF (ap2 inner_fan q r) (ap2 (Lift2 s) q r)))
      step_outer = Fan_eq inner_fan (Lift2 s) natEqF q r

      step_inner :
        Deriv (eqF (ap2 inner_fan q r)
                    (ap2 runProg (ap2 (Lift1 Fst) q r) (ap2 (Lift1 Snd) q r)))
      step_inner = Fan_eq (Lift1 Fst) (Lift1 Snd) runProg q r

      step_LF : Deriv (eqF (ap2 (Lift1 Fst) q r) (ap1 Fst q))
      step_LF = Lift1_eq Fst q r

      step_LS : Deriv (eqF (ap2 (Lift1 Snd) q r) (ap1 Snd q))
      step_LS = Lift1_eq Snd q r

      step_runProg :
        Deriv (eqF (ap2 runProg (ap2 (Lift1 Fst) q r) (ap2 (Lift1 Snd) q r))
                    (ap2 runProg (ap1 Fst q) (ap1 Snd q)))
      step_runProg =
        ruleTrans (congL runProg (ap2 (Lift1 Snd) q r) step_LF)
                  (congR runProg (ap1 Fst q) step_LS)

      step_inner_full :
        Deriv (eqF (ap2 inner_fan q r) (ap2 runProg (ap1 Fst q) (ap1 Snd q)))
      step_inner_full = ruleTrans step_inner step_runProg

      step_sr : Deriv (eqF (ap2 (Lift2 s) q r) (ap1 s r))
      step_sr = Lift2_eq s q r

      step_natEqF :
        Deriv (eqF (ap2 natEqF (ap2 inner_fan q r) (ap2 (Lift2 s) q r))
                    (ap2 natEqF (ap2 runProg (ap1 Fst q) (ap1 Snd q)) (ap1 s r)))
      step_natEqF =
        ruleTrans (congL natEqF (ap2 (Lift2 s) q r) step_inner_full)
                  (congR natEqF (ap2 runProg (ap1 Fst q) (ap1 Snd q)) step_sr)
  in ruleTrans step_outer step_natEqF

------------------------------------------------------------------------
-- At  q := Pair p l : reduces  Fst (Pair p l) -> p ,  Snd (Pair p l) -> l .

define_at_Pair_eq :
  (p l r : Term) ->
  Deriv (eqF (ap2 define (ap2 Pair p l) r)
              (ap2 natEqF (ap2 runProg p l) (ap1 s r)))
define_at_Pair_eq p l r =
  let raw :
        Deriv (eqF (ap2 define (ap2 Pair p l) r)
                    (ap2 natEqF (ap2 runProg (ap1 Fst (ap2 Pair p l))
                                              (ap1 Snd (ap2 Pair p l)))
                                  (ap1 s r)))
      raw = define_eq (ap2 Pair p l) r

      stepFst : Deriv (eqF (ap1 Fst (ap2 Pair p l)) p)
      stepFst = axFst p l

      stepSnd : Deriv (eqF (ap1 Snd (ap2 Pair p l)) l)
      stepSnd = axSnd p l

      stepRunL :
        Deriv (eqF (ap2 runProg (ap1 Fst (ap2 Pair p l))
                                  (ap1 Snd (ap2 Pair p l)))
                    (ap2 runProg p (ap1 Snd (ap2 Pair p l))))
      stepRunL = congL runProg (ap1 Snd (ap2 Pair p l)) stepFst

      stepRunR :
        Deriv (eqF (ap2 runProg p (ap1 Snd (ap2 Pair p l)))
                    (ap2 runProg p l))
      stepRunR = congR runProg p stepSnd

      stepRun :
        Deriv (eqF (ap2 runProg (ap1 Fst (ap2 Pair p l))
                                  (ap1 Snd (ap2 Pair p l)))
                    (ap2 runProg p l))
      stepRun = ruleTrans stepRunL stepRunR

      stepNatEqF :
        Deriv (eqF (ap2 natEqF (ap2 runProg (ap1 Fst (ap2 Pair p l))
                                              (ap1 Snd (ap2 Pair p l)))
                                  (ap1 s r))
                    (ap2 natEqF (ap2 runProg p l) (ap1 s r)))
      stepNatEqF = congL natEqF (ap1 s r) stepRun
  in ruleTrans raw stepNatEqF

------------------------------------------------------------------------
-- The PER-PROGRAM define_p : fixed closed p , takes  (l, r) .

define_p : Term -> Fun2
define_p p =
  Fan (Fan (Lift1 (constTermFun1 p)) (Lift1 u) runProg) (Lift2 s) natEqF

------------------------------------------------------------------------
-- The per-program equation , requiring  NoVar p .

define_p_eq :
  (p : Term) -> NoVar p -> (l r : Term) ->
  Deriv (eqF (ap2 (define_p p) l r)
              (ap2 natEqF (ap2 runProg p l) (ap1 s r)))
define_p_eq p nvp l r =
  let inner_fan : Fun2
      inner_fan = Fan (Lift1 (constTermFun1 p)) (Lift1 u) runProg

      step_outer :
        Deriv (eqF (ap2 (define_p p) l r)
                    (ap2 natEqF (ap2 inner_fan l r) (ap2 (Lift2 s) l r)))
      step_outer = Fan_eq inner_fan (Lift2 s) natEqF l r

      step_inner :
        Deriv (eqF (ap2 inner_fan l r)
                    (ap2 runProg (ap2 (Lift1 (constTermFun1 p)) l r) (ap2 (Lift1 u) l r)))
      step_inner = Fan_eq (Lift1 (constTermFun1 p)) (Lift1 u) runProg l r

      step_L1p : Deriv (eqF (ap2 (Lift1 (constTermFun1 p)) l r) (ap1 (constTermFun1 p) l))
      step_L1p = Lift1_eq (constTermFun1 p) l r

      step_const : Deriv (eqF (ap1 (constTermFun1 p) l) p)
      step_const = constTermFun1_eq p nvp l

      step_p : Deriv (eqF (ap2 (Lift1 (constTermFun1 p)) l r) p)
      step_p = ruleTrans step_L1p step_const

      step_L1u : Deriv (eqF (ap2 (Lift1 u) l r) (ap1 u l))
      step_L1u = Lift1_eq u l r

      step_u : Deriv (eqF (ap1 u l) l)
      step_u = ax_u l

      step_l : Deriv (eqF (ap2 (Lift1 u) l r) l)
      step_l = ruleTrans step_L1u step_u

      step_runProg :
        Deriv (eqF (ap2 runProg (ap2 (Lift1 (constTermFun1 p)) l r) (ap2 (Lift1 u) l r))
                    (ap2 runProg p l))
      step_runProg =
        ruleTrans (congL runProg (ap2 (Lift1 u) l r) step_p)
                  (congR runProg p step_l)

      step_inner_full :
        Deriv (eqF (ap2 inner_fan l r) (ap2 runProg p l))
      step_inner_full = ruleTrans step_inner step_runProg

      step_sr : Deriv (eqF (ap2 (Lift2 s) l r) (ap1 s r))
      step_sr = Lift2_eq s l r

      step_natEqF :
        Deriv (eqF (ap2 natEqF (ap2 inner_fan l r) (ap2 (Lift2 s) l r))
                    (ap2 natEqF (ap2 runProg p l) (ap1 s r)))
      step_natEqF =
        ruleTrans (congL natEqF (ap2 (Lift2 s) l r) step_inner_full)
                  (congR natEqF (ap2 runProg p l) step_sr)
  in ruleTrans step_outer step_natEqF
