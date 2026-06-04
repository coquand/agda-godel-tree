{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.ChaitinG1Final -- Chaitin-Goedel I, the CLEAN theorem with a TERM subject
--
--     chaitin_G1 : (x : Term) -> isNat x -> Deriv (Kgt L* x) -> ... -> Deriv falseF
--
-- ("if T proves  K(x) > L*  for some integer  x , then T is inconsistent"),
-- assembled exactly along the surprise.pdf plan:
--
--   1. ASSUME  d : Deriv (Kgt L* x)  -- T proves  K(x) > L*  for an OBJECT term  x
--      (a numeral,  isNat x ; surprise.pdf's "for some integer  x").  NO  (z : Nat) ,
--      no  natCode  -- the subject is a Term.
--   2. GET  w0  MINIMAL with  thmT(w0)  of the form  code(K(_) > L*) : the proof's
--      own code  encode d  is such a hit (T4.KFire.fireAtProof_T), so the FIRST
--      hit  w0 = firstProof x nx d  exists (T4.FirstHit -- minimality DERIVED).
--   3. READ OFF  x' = out_L w0  with  thmT(w0) = code(K(x') > L*)  (the firing, via
--      T4.KRecog.dNeg_from_hitK + the TERM-subject  negKgtCodeOf_correct_T ).
--   4. CONTRADICTION:  x'  has the SMALL DESCRIPTION  g_L* = THE LOOPING PROGRAM
--      itself -- "search for the first  K(_) > L*  proof, output its subject" -- of
--      size  c + log L*  (T4.KGodel1Canon.dLenStar).  So  K(x') <= L* , clashing
--      with  w0 's proof of  K(x') > L*  (T4.KClash.kr_clash).
--
-- STANDING ASSUMPTIONS (all granted by surprise.pdf, none a logical gap):
--   * con   : T is consistent (the clash is at the provability level -- from  w0
--             one gets  thmT w0 = code(...) , not a  Deriv  directly -- so
--             consistency is what turns "T proves false-is-provable" into the
--             stated inconsistency; this is the consistency-conditional barrier,
--             the building block the G2 surprise-exam argument consumes).
--   * nx, nOut : the assumed subject  x  and the read-off subject  out_L w0  are
--             integers (isNat -- surprise.pdf: "let  z  be the INTEGER  x  such
--             that  w  proves  K(x) > L").  Term-level numerality, not a meta Nat.
--   * nTerm, dEval : RUNNING the looping program  g_L*  until it stops --
--             evalU(parse <g_L*>, nTerm) = s (out_L w0)  -- surprise.pdf's "it is
--             easy to give a computer program that outputs  z ... and describing
--             the running of that computer program until it stops".  The ONE
--             honest black box (T proves it by Sigma_1-completeness; it is the
--             SAME looping program  g_L*  that defines  w0 / x'  in steps 2-3 and
--             serves as  x' 's short description in step 4).
--   * clOut : the read-off subject is closed (bookkeeping for the substitution).
--
-- Supersedes the object-fuel  ObjLoop  route (RETIRED): that tried to DERIVE  dEval
-- position-by-position, but its  predRun  interface (the universal interpreter
-- evaluating the  thmT -predicate at the SYMBOLIC scan variable) has an
-- uninhabited type -- so it could never be instantiated for the real predicate.
-- The honest move is to take the whole run as the single  dEval  black box.

module T4.ChaitinG1Final where

open import T4.Base
open import T4.ConInj      using ( ConSchema )
open import T4.Code        using ( codeFormula ; falseF )
open import T4.ThmT        using ( thmT )
open import T4.IsNat       using ( isNat )
open import T4.KFormula    using ( Kgt ; negKgtCodeOf ; negKgtCodeOf_correct_T )
open import T4.KRecog      using ( hitK ; hitK_le_one ; dNeg_from_hitK )
open import T4.KOut        using ( out_L )
open import T4.KFire       using ( fireAtProof_T )
open import T4.KClash      using ( kr_clash )
open import T4.KDiag       using ( gLcode )
open import T4.KGodel1Bridge using ( Lstar )
open import T4.KGodel1Canon  using ( dLenStar )
open import T4.EvalUEval   using ( evalU )
open import T4.ProgEnc     using ( enc )
open import T4.Encode      using ( encode )
open import T4.ProgParse   using ( parse )

import T4.FirstHit

------------------------------------------------------------------------
-- The assembly, at the pinned threshold  L* , parametric in Con.

module Assemble (con : Deriv ConSchema) where

  -- the recogniser  hitL = hitK L* (out_L L*)  (fires at  w  iff  thmT(w)  is of
  -- the form  code(K(out_L w) > L*) ), 0/1-valued.
  open T4.FirstHit.Search (hitK Lstar (out_L Lstar))
                            (hitK_le_one Lstar (out_L Lstar))
    using ( leastNumber ; LeastNumber )

  -- step 2: the FIRST hit (minimal proof-code of a  K(_) > L*  statement),
  -- derived from the assumed proof  d  via its own firing  fireAtProof_T .
  firstProof : (x : Term) -> isNat x -> Deriv (Kgt Lstar x) -> Term
  firstProof x nx d = LeastNumber.w1 (leastNumber (encode d) (fireAtProof_T Lstar x nx d))

  ----------------------------------------------------------------------
  -- THE THEOREM (Term subject).

  chaitin_G1 :
    (x : Term) (nx : isNat x) (d : Deriv (Kgt Lstar x)) ->
    -- step 3: the read-off subject  out_L w0  is an integer (and closed):
    isNat   (ap1 (out_L Lstar) (firstProof x nx d)) ->
    Closed  (ap1 (out_L Lstar) (firstProof x nx d)) ->
    -- step 4: running the looping program  g_L*  outputs  out_L w0  and stops:
    (nTerm : Term) -> Closed nTerm ->
    Deriv (eqF (ap2 evalU (ap1 parse (enc (gLcode Lstar))) nTerm)
               (ap1 s (ap1 (out_L Lstar) (firstProof x nx d)))) ->
    Deriv falseF
  chaitin_G1 x nx d nOut clOut nTerm clN dEval =
    let ln : LeastNumber (encode d)
        ln = leastNumber (encode d) (fireAtProof_T Lstar x nx d)
        w0 : Term
        w0 = LeastNumber.w1 ln
        zT : Term
        zT = ap1 (out_L Lstar) w0
        -- step 3:  thmT w0 = code(K(out_L w0) > L*)  (firing -> dNeg, Term subject).
        dNegOpen : Deriv (eqF (ap1 thmT w0) (codeFormula (Kgt Lstar zT)))
        dNegOpen = ruleTrans (dNeg_from_hitK Lstar (out_L Lstar) w0 (LeastNumber.isHit ln))
                             (negKgtCodeOf_correct_T Lstar zT nOut)
    in kr_clash con Lstar (enc (gLcode Lstar)) nTerm zT w0
         clN clOut dLenStar dEval dNegOpen
