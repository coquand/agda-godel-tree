{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CompressComp -- the CORRECTED Chaitin compressibility witness:
-- dPos via the COMPUTATION-naming atom (Thm13), NOT the parse/self-naming
-- atom (axRefl).  See T4/CHAITIN-KERNEL-THM13.md.
--
-- Kernel (the f(Sⁿ0)=S^{f(n)}0 analogue): the search output  y = ⟦C ell⟧  is
-- compressible because the SHORT program  C (num ell)  COMPUTES it, and T proves
-- the computation:
--
--   dPos's 2nd conjunct  =  thm13_singulary srch ell y h
--                        =  "thmT (Df ell) = ⌜ C(num ell) = num y ⌝"
--
-- with  h : C ell = y  (axRefl when  y := ap1 C ell  -- the innocuous meta
-- naming of the output; the OBJECT content is the Thm13 computation, NOT a
-- self-identity).  The subject  y  enters ONCE, as the numeral code  num y
-- (single  num  application) -- so NO double-coding, NO  codeTermF .
--
-- The barrier (chaitinBarrierFinishComp) is the SAME (A)∧(B) skeleton as the
-- shipped CompressCanonical.chaitinBarrierFinish (two encoded_mp + dExFGen +
-- ConSchema + axExFalso); only the atom  A  and  dPos  change.  C is left
-- ABSTRACT (a Fun1 parameter) -- the kernel needs no concrete chaitinSearch;
-- instantiate  C := chaitinSearch  later.

module T4.CompressComp where

open import T4.Base
open import T4.Code using ( codeFormula ; codeFalse ; falseF )
open import T4.LenR using ( lenR )
open import T4.ThmT using ( thmT )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.DefWit using ( cImp ; dExFGen )
open import T4.DefWitComp
  using ( atomFormCompAt ; nameEqCodeComp ; nameEqComp_roundtrip )
open import T4.IsNat using ( isNat )
open import T4.ConInj using ( ConSchema ; cmp )
open import T4.CompressCanonical using ( andIntro )
open import T4.ParseRoundtrip using ( linTop )
open import T4.Thm12.EncodedMp using ( encoded_mp )
open import T4.Thm12.All using ( thm12 ; fst )
open import T4.Thm12.Thm13 using ( thm13_singulary ; codeFXeqY1 )

open import BRA3.ChurchLeq using ( leq )
open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- SECTION 1.  The computation-naming compressibility atom (closed).
--
-- Re-pointed (NEXT-SESSION-CHAITIN-G1 Step 2a): the atom is now the SHARED
-- DefWitComp.atomFormCompAt , with the canonical name  nameT := linTop (ap1
-- srch ell)  and proof  prf := Df ell  pinned in, so  dPos  (here) and  dNeg
-- (the search side) refer to the SAME formula.  Concretely
--
-- atomComp ell srch y  =
--   (lenR (linTop (ap1 srch ell)) <= ell)                 -- the name fits ell (dLen)
--   AND
--   (thmT (Df ell) = ⌜ srch(num ell) = num y ⌝)           -- T proves the computation
--
-- where  Df = fst (thm12 srch)  is the canonical proof-code builder.  The
-- 2nd conjunct's code is now  nameEqCodeComp (linTop (ap1 srch ell)) y  (the
-- search-compatible single- num  form), which  nameEqComp_roundtrip  proves
-- equal to the  codeFXeqY1 srch ell y  that  thm13_singulary  produces.

atomComp : (ell : Term) (srch : Fun1) (y : Term) -> Formula
atomComp ell srch y =
  atomFormCompAt ell (linTop (ap1 srch ell)) (ap1 (fst (thm12 srch)) ell) y

------------------------------------------------------------------------
-- SECTION 2.  The object proof of the closed atom, and dPos.
--
-- compressProofComp  builds  Deriv (atomComp ...)  by And-introduction of:
--   * dLen   : Deriv (lenR (linTop (ap1 srch ell)) <= ell)  -- the length premise
--   * 2nd conjunct : Deriv (thmT (Df ell) = nameEqCodeComp (linTop (ap1 srch ell)) y)
--       =  thm13_singulary srch ell y h            -- targets codeFXeqY1 srch ell y
--          rewritten by  ruleSym (nameEqComp_roundtrip srch ell y eN)  into the
--          search-compatible  nameEqCodeComp  form (the eN : isNat ell consumed
--          here is the numeral side-condition of the roundtrip).
-- Then dPos necessitates the whole conjunction once (thmT_complete_rec).

compressProofComp :
  (ell : Term) (srch : Fun1) (y : Term) ->
  isNat ell ->                                       -- eN: ell is a numeral
  Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell) ->   -- dLen
  Deriv (eqF (ap1 srch ell) y) ->                    -- h: the computation
  Deriv (atomComp ell srch y)
compressProofComp ell srch y eN dLen h =
  let secondConjunct :
        Deriv (eqF (ap1 thmT (ap1 (fst (thm12 srch)) ell))
                   (nameEqCodeComp (linTop (ap1 srch ell)) y))
      secondConjunct =
        ruleTrans (thm13_singulary srch ell y h)
                  (ruleSym (nameEqComp_roundtrip srch ell y eN))
  in andIntro (leq (ap1 lenR (linTop (ap1 srch ell))) ell)
              (eqF (ap1 thmT (ap1 (fst (thm12 srch)) ell))
                   (nameEqCodeComp (linTop (ap1 srch ell)) y))
              dLen
              secondConjunct

-- the canonical compressibility proof code.
cPosComp :
  (ell : Term) (srch : Fun1) (y : Term) ->
  isNat ell ->
  Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell) ->
  Deriv (eqF (ap1 srch ell) y) ->
  Term
cPosComp ell srch y eN dLen h = encode (compressProofComp ell srch y eN dLen h)

-- dPos (corrected):  thmT proves the closed computation-naming atom of  y .
dPosComp :
  (ell : Term) (srch : Fun1) (y : Term)
  (eN : isNat ell)
  (dLen : Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell))
  (h : Deriv (eqF (ap1 srch ell) y)) ->
  Deriv (eqF (ap1 thmT (cPosComp ell srch y eN dLen h))
             (codeFormula (atomComp ell srch y)))
dPosComp ell srch y eN dLen h =
  thmT_complete_rec (compressProofComp ell srch y eN dLen h)

------------------------------------------------------------------------
-- SECTION 3.  chaitinBarrierFinishComp -- the Chaitin barrier for the
-- computation-named subject.  SAME skeleton as
-- CompressCanonical.chaitinBarrierFinish: dPos (B) + dExFGen + Stage 3
-- (two encoded_mp + ConSchema + axExFalso), with the corrected atom.  The
-- ONLY abstract input is  dNeg  -- "thmT proves the atom is FALSE" -- which
-- is the bounded search's output (KR-B), at the SAME closed atom (§7
-- alignment).

chaitinBarrierFinishComp :
  Deriv ConSchema ->
  (ell : Term) (srch : Fun1) (y : Term) ->
  (eN : isNat ell) ->                                  -- ell is a numeral
  (dLen : Deriv (leq (ap1 lenR (linTop (ap1 srch ell))) ell)) ->  -- the name fits ell
  (h : Deriv (eqF (ap1 srch ell) y)) ->                   -- y := the output (computation)
  (pNeg : Term) ->
  Deriv (eqF (ap1 thmT pNeg)                            -- the search's output:
             (codeFormula (neg (atomComp ell srch y)))) ->
  Deriv falseF
chaitinBarrierFinishComp con ell srch y eN dLen h pNeg dNeg =
  let A : Formula
      A = atomComp ell srch y
      cPos : Term
      cPos = cPosComp ell srch y eN dLen h
      cExF : Term
      cExF = encode (axExFalso A falseF)
      consImp : Term                                   -- code of  (neg A -> false)
      consImp = cImp (codeFormula (neg A)) codeFalse
      -- thmT proves  (neg A -> false)   [MP of dExFGen, dPos].
      mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos)) consImp)
      mp1 = encoded_mp cExF cPos (codeFormula A) consImp
              (dExFGen A) (dPosComp ell srch y eN dLen h)
      -- thmT proves  false              [MP of mp1, dNeg].
      finalProof : Term
      finalProof = cmp (cmp cExF cPos) pNeg
      mp2 : Deriv (eqF (ap1 thmT finalProof) codeFalse)
      mp2 = encoded_mp (cmp cExF cPos) pNeg (codeFormula (neg A)) codeFalse mp1 dNeg
      -- Con refutes it.
      con_inst : Deriv (neg (eqF (ap1 thmT finalProof) codeFalse))
      con_inst = ruleInst zero finalProof con
  in mp (mp (axExFalso (eqF (ap1 thmT finalProof) codeFalse) falseF) mp2) con_inst
