{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CKProg -- the CONCRETE characteristic program CK of surprise-GII and its
-- bare-argument atom.  (Task (a), subtask 2 of T4/SURPRISE-GII-HANDOFF.md:
-- Kr / CK is a closed total combinator, NOT abstract.)
--
-- K is DECIDABLE (a finite conjunction of bounded, l-step run-negations over the
-- finite program set  S = enum ), hence a TOTAL characteristic function -- so it
-- is literally an element of  Fun2 , with the subject  u  and the run-length  x
-- both BARE arguments (no mu-search, nothing to "close"; the forall-l of
-- incompressibility lives at the FORMULA level, x left free).  clos-corrected.md:
--
--   CK : Fun2 ,   ap2 CK u x = O   iff   some p in enum defines u in x steps.
--
-- Built from the concrete pieces of  T4.DefInd  (the define indicator  defInd
-- and its disjunction fold  defCount = sumRec defInd enum ) plus one  isZero
-- flip (native  O = false / s O = true , so a nonzero match-count flips to  O ,
-- matching clos's  O = "compressible"):
--
--   CK = Post isZero (Fan pi (Lift1 (constN N)) (defCount enum))
--   ap2 CK u x = isZero ( ap2 (defCount enum) (pi u x) (natCode N) )            (PROVED)
--             = isZero ( sum_{j=0}^{N} defInd(enum j, pi u x) ) .
--
-- The atom is then the bare-argument characteristic equation (clos's "one
-- definitional condition"), with BOTH variables bare so  encode  exposes them as
-- cVarc  leaves under  cAp2f CK  (no  num  baked in; Step 2 installs  ap1 num x0
-- by substitution):
--
--   charAtom2 x0 x1 = eqF (ap2 CK (var x0) (var x1)) O
--   codeFormula (charAtom2 x0 x1) = cEqTm (cAp2f CK (cVarc x0) (cVarc x1)) O     (refl).
--
-- enum : Fun1  and the meta count  N  are parameters (the enumerator is the
-- concrete  T4.EnumProg.enum , supplied downstream;  N := Bnat  at the margin);
-- CK itself is a closed combinator given them.  CK's VALUE-correctness (that it
-- is  O  exactly at compressible subjects) is established at the run-witness
-- sites (Steps 1/4/6), not here.

module T4.CKProg where

open import T4.Base
open import BRA3.Church   using ( isZero ; pi )
open import BRA3.Dispatch using ( constN ; constN_eq )
open import T4.Num        using ( num )
open import T4.Code       using ( codeFormula ; codeTerm )
open import T4.DefWit     using ( cEqTm ; cNeg )
open import T4.CgiClash   using ( cAp2f ; cVarc )
open import T4.DefInd     using ( defCount )

-- enum : the (concrete) enumerator of Berry's finite program set;  N : the meta
-- program-count margin ( N := Bnat  downstream).
module _ (enum : Fun1) (N : Nat) where

  ----------------------------------------------------------------------
  -- SECTION 1.  The concrete characteristic program  CK : Fun2 .

  CK : Fun2
  CK = Post isZero (Fan pi (Lift1 (constN N)) (defCount enum))

  -- ap2 CK u x = isZero ( ap2 (defCount enum) (pi u x) (natCode N) )   (PROVED).
  -- (uT = subject, xT = run-length; named to avoid the BRA combinators u / v.)
  CK_eq :
    (uT xT : Term) ->
    Deriv (eqF (ap2 CK uT xT)
               (ap1 isZero (ap2 (defCount enum) (ap2 pi uT xT) (natCode N))))
  CK_eq uT xT =
    let ePost : Deriv (eqF (ap2 CK uT xT)
                           (ap1 isZero (ap2 (Fan pi (Lift1 (constN N)) (defCount enum)) uT xT)))
        ePost = axPost isZero (Fan pi (Lift1 (constN N)) (defCount enum)) uT xT

        eFan : Deriv (eqF (ap2 (Fan pi (Lift1 (constN N)) (defCount enum)) uT xT)
                          (ap2 (defCount enum) (ap2 pi uT xT)
                                               (ap2 (Lift1 (constN N)) uT xT)))
        eFan = axFan pi (Lift1 (constN N)) (defCount enum) uT xT

        eIdx : Deriv (eqF (ap2 (Lift1 (constN N)) uT xT) (natCode N))
        eIdx = ruleTrans (axLift (constN N) uT xT) (constN_eq N uT)

        eRange : Deriv (eqF (ap2 (defCount enum) (ap2 pi uT xT) (ap2 (Lift1 (constN N)) uT xT))
                            (ap2 (defCount enum) (ap2 pi uT xT) (natCode N)))
        eRange = congR (defCount enum) (ap2 pi uT xT) eIdx
    in ruleTrans ePost
         (cong1 isZero (ruleTrans eFan eRange))

  ----------------------------------------------------------------------
  -- SECTION 2.  The bare-argument characteristic atom (cAp2f, two bare vars).
  --   All code identities by  refl  ( codeFormula / codeTerm  match
  --   cEqTm / cAp2f / cVarc / cNeg ; cO = codeTerm O = O ).

  charAtom2 : Nat -> Nat -> Formula
  charAtom2 i0 i1 = eqF (ap2 CK (var i0) (var i1)) O

  charAtomCode2 : Term -> Term -> Term
  charAtomCode2 s0 s1 = cEqTm (cAp2f CK s0 s1) O

  -- Encode side: both subjects sit as BARE  cVarc  leaves under  cAp2f CK .
  charAtom2_at_vars :
    (i0 i1 : Nat) ->
    Eq (codeFormula (charAtom2 i0 i1)) (charAtomCode2 (cVarc i0) (cVarc i1))
  charAtom2_at_vars i0 i1 = refl

  -- Step-2 target: subject installed num-raw  ap1 num x0 , run-length still
  -- coded  cVarc x1  ( sbt_at_var_match  on x0,  sbt_at_var_nomatch  on x1).
  charAtomCode2_num_subj :
    (x0 : Term) (i1 : Nat) ->
    Eq (charAtomCode2 (ap1 num x0) (cVarc i1))
       (cEqTm (cAp2f CK (ap1 num x0) (cVarc i1)) O)
  charAtomCode2_num_subj x0 i1 = refl

  ----------------------------------------------------------------------
  -- SECTION 3.  The negated atom -- the stage predicate body
  --   S(r) := Deriv (neg (eqF (ap2 CK (var x0) (var x1)) O)) .

  charNeg2 : Nat -> Nat -> Formula
  charNeg2 i0 i1 = neg (charAtom2 i0 i1)

  charNegCode2 : Term -> Term -> Term
  charNegCode2 s0 s1 = cNeg (charAtomCode2 s0 s1)

  charNeg2_at_vars :
    (i0 i1 : Nat) ->
    Eq (codeFormula (charNeg2 i0 i1)) (cNeg (cEqTm (cAp2f CK (cVarc i0) (cVarc i1)) O))
  charNeg2_at_vars i0 i1 = refl
