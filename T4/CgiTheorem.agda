{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiTheorem -- CGI num-raw, the CAPSTONE: Theorem 1 of
-- cgi-numraw-statement.tex (the Con-free core).
--
-- The faithful rendering carries EXACTLY the surprise.pdf ingredients:
--   (1) the generic while-loop  g  with the recogniser  p = hitKdef  applied
--       DIRECTLY (= T4.FirstHit.Search.g, equations g_at_O / g_at_succ);
--   (2) the least-number lemma (T4.FirstHit.leastNumber) supplying firstness;
--   (3) the size choice  c + log L0 < L0  (T4.KGodel1Canon.dLenStar at the
--       canonical  L0 := Lstar ), the subject kept as the TERM the program
--       outputs ( x' := outKdef Lstar w0 ).
--
-- From a SINGLE provability fact  thmT w = code(K(x_) > L0)  the recogniser
-- fires at w, the least-number lemma returns the FIRST hit w0, its subject is
-- read off  x' := outKdef Lstar w0  (num-raw), the recogniser re-delivers the
-- open negative leg, and the clash produces  z  with  thmT z = code(0=1) .
--
-- The size fact is NOT a hypothesis: L0 is introduced precisely so that
-- |g_{L0}| <= L0 is TRUE and PROVABLE -- here DERIVED by Sigma1-completeness
-- (Thm13) from the shipped  dLenStar .  No size hypothesis, no Con corollary.

module T4.CgiTheorem where

open import T4.Base
open import T4.Tags       using ( tag_eq ; tag_ap1 ; tag_s )
open import T4.Code       using ( codeFun1 )
open import T4.ThmT       using ( thmT )
open import T4.Num        using ( num ; num_at_O ; num_at_S )
open import T4.DefWit     using ( cEqTm )
open import T4.Kdef       using ( Kcode )
open import T4.KdefRecog  using
  ( outKdef ; hitKdef ; hitKdef_le_one ; hitKdef_fires ; dNeg_from_hitKdef )
open import T4.CgiClash   using ( SomeProof ; szAtomT ; cgiClash ; cAp1f )
open import T4.EvalUEval  using ( evalU )
open import T4.ProgParse  using ( parse )
open import T4.FirstHit   using ( module Search )
open import T4.KFormula   using ( szLeqFun ; szLeqApp )
open import T4.KGodel1Canon using ( dLenStar )
open import T4.KGodel1Bridge using ( Lstar )
open import T4.KDiag      using ( gLcode )
open import T4.ProgEnc    using ( enc )
open import T4.Thm12.Thm13 using ( codeFXeqY1 ; thm13_singulary )
open import T4.Thm12.All   using ( thm12 ; fst )

------------------------------------------------------------------------
-- The canonical short program NAME (Step 3): the encoding of the search
-- loop  gLcode Lstar  whose size  dLenStar  proves fits  L0 = Lstar .

gLname : Term
gLname = enc (gLcode Lstar)

------------------------------------------------------------------------
-- Step 3 PROVED: T proves  szLeq(num gLname) = 1 .  (NOT a hypothesis.)
--
-- Sigma1-completeness (Thm13) internalises the shipped size fact  dLenStar
-- (= ingredient (3), the choice  c + log L0 < L0 ) num-raw; the codeFXeqY1
-- RHS  num (s 0)  is bridged to the formula's literal  s 0  by num_at_S/O.

cSizeProof : Term
cSizeProof = ap1 (fst (thm12 (szLeqFun Lstar))) gLname

-- the code of  szLeq(num gLname) = 1  (= szAtomT Lstar gLname _ _ (num gLname)).
szLeqClosed : Term
szLeqClosed = cEqTm (cAp1f (szLeqFun Lstar) (ap1 num gLname)) (cAp1f s O)

dSize : Deriv (eqF (ap1 thmT cSizeProof) szLeqClosed)
dSize =
  let -- RHS bridge:  num (s 0) = code(s)(num 0) = code(s) 0 .
      bRHS : Deriv (eqF (ap1 num (ap1 s O)) (cAp1f s O))
      bRHS = ruleTrans (num_at_S O)
               (congR Pair (natCode tag_ap1) (congR Pair (natCode tag_s) num_at_O))
      -- codeFXeqY1 (szLeqFun Lstar) gLname (s 0) = szLeqClosed.
      bridge : Deriv (eqF (codeFXeqY1 (szLeqFun Lstar) gLname (ap1 s O)) szLeqClosed)
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp1f (szLeqFun Lstar) (ap1 num gLname)) bRHS)
  in ruleTrans (thm13_singulary (szLeqFun Lstar) gLname (ap1 s O) dLenStar) bridge

------------------------------------------------------------------------
-- The least-number search at the K-recogniser p = hitKdef Lstar (outKdef Lstar).

open Search (hitKdef Lstar (outKdef Lstar)) (hitKdef_le_one Lstar (outKdef Lstar))

-- ingredients (1)+(2): the FIRST hit  w0  and the subject  x' := outKdef Lstar w0 .
firstHit : (w x : Term) -> Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)) -> Term
firstHit w x hyp = LeastNumber.w1 (leastNumber w (hitKdef_fires Lstar w x hyp))

subjOf : (w x : Term) -> Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x)) -> Term
subjOf w x hyp = ap1 (outKdef Lstar) (firstHit w x hyp)

-- the open negative leg at the first hit:  thmT w0 = ap1 (Kcode Lstar) x' .
dNegAt :
  (w x : Term) (hyp : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))) ->
  Deriv (eqF (ap1 thmT (firstHit w x hyp))
             (ap1 (Kcode Lstar) (subjOf w x hyp)))
dNegAt w x hyp =
  dNeg_from_hitKdef Lstar (outKdef Lstar) (firstHit w x hyp)
    (LeastNumber.isHit (leastNumber w (hitKdef_fires Lstar w x hyp)))

------------------------------------------------------------------------
-- Theorem 1 (Con-free core).  Size DERIVED; only the run remains an input
-- (the surprise.pdf "computer program that outputs z, run until it stops" --
-- ingredient (1), to be derived from g's equations + leastNumber).

chaitin_G1 :
  (w x n0 : Term) ->
  (hyp : Deriv (eqF (ap1 thmT w) (ap1 (Kcode Lstar) x))) ->
  -- the loop's output, run until it stops (ingredient (1), single halt fact).
  Deriv (eqF (ap2 evalU (ap1 parse gLname) n0) (ap1 s (subjOf w x hyp))) ->
  SomeProof
chaitin_G1 w x n0 hyp run =
  cgiClash Lstar gLname n0 (subjOf w x hyp) (firstHit w x hyp) cSizeProof
    (dNegAt w x hyp) dSize run
