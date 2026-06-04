{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CheckAlphN -- a DEPTH-INDEXED object validity checker for program-code
-- strings, designed so that  checkAlphN n p = s O  ENTAILS the structural
-- decomposition of  p  WITHOUT any surjective-pairing law for  pi .
--
-- =====================================================================
-- THE METHOD ( the structural witness comes from the checker, not from a
-- universal  pi (Fst p)(Snd p) = p ).
-- =====================================================================
--
-- We build a RECONSTRUCTION functor  reconF n : Fun1  whose value at  p  is
-- the canonical depth-<= n code that  p  WOULD be if valid, assembled purely
-- from  p 's projections  ( Fst / Snd ) :
--
--   reconF 0       p = O
--   reconF (suc n) p = if   Fst p = natCode 1   then pi (natCode 1) (reconF n (Snd p))
--                      elif Fst p = natCode 2   then pi (natCode 2) (reconF n (Snd p))
--                      elif Fst p = natCode 3   then pi (natCode 3) (reconF n (Snd p))
--                      else                          O
--
-- and DEFINE the checker as the single equality test
--
--   checkAlphN n p = natEqF p (reconF n p) .
--
-- Then  checkAlphN n p = s O   reflects ( T4.NatEqSoundImp.natEqF_sound_imp )
-- into the OBJECT equation  p = reconF n p .   Because the canonical
-- reconstruction carries the valid head  natCode i  and the  pi -shape
-- LITERALLY, this equation hands the coverage induction the cell decomposition
-- p = pi (natCode i) (Snd p)  with a valid tag and a shorter valid tail -- the
-- structure that, over a free  p , a raw checker could only get from surjective
-- pairing.   No  pi -surjectivity is used : the reject branch reconstructs to
-- O , and the leaf  O = pi O O  ( Fst O = O not in {1,2,3} ) routes there too,
-- so  reconF (suc n) O = O = O  and  O  passes its own equality test while a
-- malformed  p  fails it ( natEqF p O = O  since  p /= O ).
--
-- This file ships the DEFINITION and its REDUCTION equations ( the algebra ).
-- The coverage theorem ( internal correctness of  enum ) is  T4.InternalCover .

module T4.CheckAlphN where

open import T4.Base

open import BRA3.Church       using ( pi )
open import BRA3.ChurchT117   using ( Fst )
open import BRA3.ChurchT116   using ( Snd )
open import BRA3.SubT.NatEq   using ( natEqF )
open import BRA3.PairAlgebra  using ( Pair ; I ; axI ; Z ; axZ ; compose1U ; compose1U_eq )
open import BRA3.Dispatch     using ( condFork ; constN ; constN_eq )

------------------------------------------------------------------------
-- SECTION 1.  The reconstruction functor and the checker.

-- guard :  ap1 (gtag i) p = natEqF (Fst p) (natCode i) .
gtag : Nat -> Fun1
gtag i = C natEqF Fst (constN i)

-- cell :  ap1 (cellOf i rn) p = pi (natCode i) (rn (Snd p)) .
cellOf : Nat -> Fun1 -> Fun1
cellOf i rn = C pi (constN i) (compose1U rn Snd)

-- The inner cascade levels (head = 3, head = 2, then the full body).
cell3Fun : Fun1 -> Fun1
cell3Fun rn =
  C condFork (C Pair (cellOf 3 rn) Z) (gtag 3)

cell2Fun : Fun1 -> Fun1
cell2Fun rn =
  C condFork (C Pair (cellOf 2 rn) (cell3Fun rn)) (gtag 2)

cell1Fun : Fun1 -> Fun1
cell1Fun rn =
  C condFork (C Pair (cellOf 1 rn) (cell2Fun rn)) (gtag 1)

reconF : Nat -> Fun1
reconF zero    = Z
reconF (suc n) = cell1Fun (reconF n)

checkAlphN : Nat -> Fun1
checkAlphN n = C natEqF I (reconF n)

------------------------------------------------------------------------
-- SECTION 2.  Reduction equations (the algebra).

-- checkAlphN n p = natEqF p (reconF n p).
checkAlphN_eq :
  (n : Nat) (p : Term) ->
  Deriv (eqF (ap1 (checkAlphN n) p) (ap2 natEqF p (ap1 (reconF n) p)))
checkAlphN_eq n p =
  ruleTrans (ax_C natEqF I (reconF n) p)
            (congL natEqF (ap1 (reconF n) p) (axI p))

-- reconF 0 p = O.
reconF_zero_eq : (p : Term) -> Deriv (eqF (ap1 (reconF zero) p) O)
reconF_zero_eq p = axZ p

-- gtag i p = natEqF (Fst p) (natCode i).
gtag_eq :
  (i : Nat) (p : Term) ->
  Deriv (eqF (ap1 (gtag i) p) (ap2 natEqF (ap1 Fst p) (natCode i)))
gtag_eq i p =
  ruleTrans (ax_C natEqF Fst (constN i) p)
            (congR natEqF (ap1 Fst p) (constN_eq i p))

-- cellOf i rn p = pi (natCode i) (rn (Snd p)).
cellOf_eq :
  (i : Nat) (rn : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (cellOf i rn) p)
              (ap2 pi (natCode i) (ap1 rn (ap1 Snd p))))
cellOf_eq i rn p =
  ruleTrans (ax_C pi (constN i) (compose1U rn Snd) p)
    (ruleTrans (congL pi (ap1 (compose1U rn Snd) p) (constN_eq i p))
               (congR pi (natCode i) (compose1U_eq rn Snd p)))

-- The three cascade unfoldings, generic in the recursion functor  rn .
-- cell1Fun rn p = condFork (Pair (cellOf 1 rn p) (cell2Fun rn p)) (natEqF (Fst p)(natCode 1))
cell1_eq :
  (rn : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (cell1Fun rn) p)
              (ap2 condFork
                 (ap2 Pair (ap1 (cellOf 1 rn) p) (ap1 (cell2Fun rn) p))
                 (ap2 natEqF (ap1 Fst p) (natCode 1))))
cell1_eq rn p =
  let pf : Fun1
      pf = C Pair (cellOf 1 rn) (cell2Fun rn)
      e1 : Deriv (eqF (ap1 (cell1Fun rn) p)
                       (ap2 condFork (ap1 pf p) (ap1 (gtag 1) p)))
      e1 = ax_C condFork pf (gtag 1) p
      e2 : Deriv (eqF (ap1 pf p)
                       (ap2 Pair (ap1 (cellOf 1 rn) p) (ap1 (cell2Fun rn) p)))
      e2 = ax_C Pair (cellOf 1 rn) (cell2Fun rn) p
  in ruleTrans e1
       (ruleTrans (congL condFork (ap1 (gtag 1) p) e2)
                  (congR condFork
                     (ap2 Pair (ap1 (cellOf 1 rn) p) (ap1 (cell2Fun rn) p))
                     (gtag_eq 1 p)))

cell2_eq :
  (rn : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (cell2Fun rn) p)
              (ap2 condFork
                 (ap2 Pair (ap1 (cellOf 2 rn) p) (ap1 (cell3Fun rn) p))
                 (ap2 natEqF (ap1 Fst p) (natCode 2))))
cell2_eq rn p =
  let pf : Fun1
      pf = C Pair (cellOf 2 rn) (cell3Fun rn)
      e1 : Deriv (eqF (ap1 (cell2Fun rn) p)
                       (ap2 condFork (ap1 pf p) (ap1 (gtag 2) p)))
      e1 = ax_C condFork pf (gtag 2) p
      e2 : Deriv (eqF (ap1 pf p)
                       (ap2 Pair (ap1 (cellOf 2 rn) p) (ap1 (cell3Fun rn) p)))
      e2 = ax_C Pair (cellOf 2 rn) (cell3Fun rn) p
  in ruleTrans e1
       (ruleTrans (congL condFork (ap1 (gtag 2) p) e2)
                  (congR condFork
                     (ap2 Pair (ap1 (cellOf 2 rn) p) (ap1 (cell3Fun rn) p))
                     (gtag_eq 2 p)))

cell3_eq :
  (rn : Fun1) (p : Term) ->
  Deriv (eqF (ap1 (cell3Fun rn) p)
              (ap2 condFork
                 (ap2 Pair (ap1 (cellOf 3 rn) p) O)
                 (ap2 natEqF (ap1 Fst p) (natCode 3))))
cell3_eq rn p =
  let pf : Fun1
      pf = C Pair (cellOf 3 rn) Z
      e1 : Deriv (eqF (ap1 (cell3Fun rn) p)
                       (ap2 condFork (ap1 pf p) (ap1 (gtag 3) p)))
      e1 = ax_C condFork pf (gtag 3) p
      e2 : Deriv (eqF (ap1 pf p)
                       (ap2 Pair (ap1 (cellOf 3 rn) p) (ap1 Z p)))
      e2 = ax_C Pair (cellOf 3 rn) Z p
      e3 : Deriv (eqF (ap2 Pair (ap1 (cellOf 3 rn) p) (ap1 Z p))
                       (ap2 Pair (ap1 (cellOf 3 rn) p) O))
      e3 = congR Pair (ap1 (cellOf 3 rn) p) (axZ p)
  in ruleTrans e1
       (ruleTrans (congL condFork (ap1 (gtag 3) p) (ruleTrans e2 e3))
                  (congR condFork
                     (ap2 Pair (ap1 (cellOf 3 rn) p) O)
                     (gtag_eq 3 p)))

-- reconF (suc n) p = the level-1 cascade.
reconF_suc_eq :
  (n : Nat) (p : Term) ->
  Deriv (eqF (ap1 (reconF (suc n)) p)
              (ap2 condFork
                 (ap2 Pair (ap1 (cellOf 1 (reconF n)) p) (ap1 (cell2Fun (reconF n)) p))
                 (ap2 natEqF (ap1 Fst p) (natCode 1))))
reconF_suc_eq n p = cell1_eq (reconF n) p
