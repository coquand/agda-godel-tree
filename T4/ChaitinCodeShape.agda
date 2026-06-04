{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinCodeShape -- the coherence PROBE for the Chaitin G1 search bridge
-- (CHAITIN-G1-SEARCH-DESIGN.md, step 1, validate-by-construction).
--
-- The user's caution: the bridge's risk is the Num/codeTerm-at-substitution
-- coherence.  This file CONFIRMS, machine-checked, the central claim of the
-- design note: the subject  x  of the DefWit atom appears DOUBLE-CODED, as
-- codeTerm (codeTerm x) , in  codeFormula (neg (atomForm ell x)) .  That double-
-- coding (inherent: the atom asserts thmT-provability of a formula MENTIONING
-- the subject) is what forces an OBJECT coding functor  codeTermF : Fun1  on
-- the search side, and is the locus of the genuine content lemma.
--
-- If these  refl s typecheck, the §1 shape analysis is correct and interface
-- (B) (pair-enumeration + codeTermF) is the validated route.

module T4.ChaitinCodeShape where

open import T4.Base
open import T4.Tags using ( tag_eq ; tag_ap2 )
open import T4.Code using ( codeTerm ; codeFun2 )
open import T4.DefWit using ( cEqTm ; cV0 ; subjCode )

------------------------------------------------------------------------
-- The subject double-codes:  codeTerm (subjCode x)  has  codeTerm (codeTerm x)
-- as the leaf in its right-most slot.  subjCode x = cEqTm cV0 (codeTerm x) =
-- ap2 Pair (natCode tag_eq) (ap2 Pair cV0 (codeTerm x)) , and  codeTerm  unfolds
-- structurally on the two  ap2 Pair  nodes until it reaches the neutral leaf
-- codeTerm (codeTerm x) .

subj_doublecodes :
  (x : Term) ->
  Eq (codeTerm (subjCode x))
     (ap2 Pair (natCode tag_ap2)
        (ap2 Pair (codeFun2 Pair)
          (ap2 Pair (codeTerm (natCode tag_eq))
            (ap2 Pair (natCode tag_ap2)
              (ap2 Pair (codeFun2 Pair)
                (ap2 Pair (codeTerm cV0) (codeTerm (codeTerm x))))))))
subj_doublecodes x = refl

------------------------------------------------------------------------
-- The hole is reached by a FIXED path of  Snd / Fst  projections from
-- codeTerm (subjCode x) :  the right-most leaf is exactly  codeTerm (codeTerm x).
-- (Documents that an object recogniser/builder can target it by a fixed path;
--  the value at the hole is the doubly-coded subject, confirming the design.)

subj_hole :
  (x : Term) ->
  Eq (codeTerm (subjCode x))
     (ap2 Pair (natCode tag_ap2)
        (ap2 Pair (codeFun2 Pair)
          (ap2 Pair (codeTerm (natCode tag_eq))
            (codeTerm (ap2 Pair cV0 (codeTerm x))))))
subj_hole x = refl
