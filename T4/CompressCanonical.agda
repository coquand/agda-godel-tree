{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CompressCanonical -- the remaining KR-A content: building the canonical
-- compressibility witness for the Chaitin output  (the  dPos  argument of
-- SpikeChaitin.chaitin_thm).
--
-- The Chaitin machine's output  y = chaitinSearch <ell>  is compressible
-- because  y  NAMES ITSELF: the short description term  g* = y  satisfies the
-- defining biconditional  (v0 = g*) <-> (v0 = y)  trivially (reflexivity).
-- So the canonical name is  Flin* = linTop y  and the canonical proof is
-- pi* = encode (iffReflProof (v0 = y)) , and the genuinely-new content is the
-- single  dSecondConjunct : "thmT proves the naming biconditional via pi*",
-- the SECOND conjunct of  atomForm  instantiated at  (Flin*, pi*).
--
-- This is NOT a weakening (it is the faithful Chaitin step): the description
-- term  g* = chaitinSearch <ell>  is SHORT (lenR (linTop g*) = const + O(log
-- ell) <= ell), so it pins a HUGE  y  via a SHORT name -- the proof  pi*  of
-- the reflexive biconditional is itself short, and the "long proof" the Berry
-- paradox needs is the SEARCH (chaitinSearch reaching the incompressibility
-- proof), not the naming.  Σ₁-completeness: T proves the naming directly.
--
-- This file builds the propositional And-introduction (the Formula layer has
-- no native And), the reflexive biconditional, and  dSecondConjunct .  The
-- thmT-level necessitation (representability of  thmT  at  pi* ) and the
-- And-introduction at the thmT level (combining with the lenR bound to give
-- dPos ) are the next step -- see NEXT-SESSION-KR-A-COMPRESS-CANONICAL.md.

module T4.CompressCanonical where

open import T4.Base
open import T4.Code using ( codeFormula )
open import T4.LenR using ( lenR )
open import T4.ThmT using ( thmT )
open import T4.Encode using ( encode )
open import T4.ThmTCompleteRec using ( thmT_complete_rec )
open import T4.ParseRoundtrip using ( linTop )
open import T4.DefWit
  using ( cImp ; nameEqCode ; nameEq_roundtrip ; atomFormAt ; dExFGen )
open import T4.Code using ( codeFalse ; falseF )
open import T4.ConInj using ( ConSchema ; cmp )
open import T4.Thm12.EncodedMp using ( encoded_mp )

open import BRA3.ChurchLeq using ( leq )
open import BRA3.Equational using ( axRefl )
open import BRA3.Contrapositive
  using ( identP ; liftP ; bComb ; Q_to_dNeg ; axContrapos ; axExFalso )

------------------------------------------------------------------------
-- SECTION 1.  Propositional And-introduction (the Formula layer has only
-- atomic / neg / imp, so  fAnd A B = neg (imp A (neg B)) ).
--
--   From  da : A  and  db : B , derive  neg (imp A (neg B)) :
--   let  X = imp A (neg B) ;  X -> A  (da is a theorem),  X -> X  is  X -> (A
--   -> neg B), so  X -> neg B ; and  neg (neg B)  is a theorem (db); contrapose
--    X -> neg B  to  neg (neg B) -> neg X , then mp.

andIntro :
  (A B : Formula) -> Deriv A -> Deriv B -> Deriv (neg (imp A (neg B)))
andIntro A B da db =
  let X : Formula
      X = imp A (neg B)
      dXA : Deriv (imp X A)
      dXA = liftP X da
      dX_nB : Deriv (imp X (neg B))
      dX_nB = bComb (identP X) dXA
      dNNB : Deriv (neg (neg B))
      dNNB = mp (Q_to_dNeg B) db
      cp : Deriv (imp (imp X (neg B)) (imp (neg (neg B)) (neg X)))
      cp = axContrapos X (neg B)
  in mp (mp cp dX_nB) dNNB

------------------------------------------------------------------------
-- SECTION 3.  The canonical proof  pi*  and the naming fact (term-equality).
--
-- The Chaitin output  x  NAMES ITSELF: the description term  g = x , so the
-- naming formula  "g = x"  is  "x = x" , proved by  axRefl x  (Church Thm 10).
--   piStar x = encode (axRefl x)   -- the short canonical proof of  x = x .
--   thmT (piStar x) = codeFormula (eqF x x)            [thmT_complete_rec]
--                   = nameEqCode (linTop x) x          [nameEq_roundtrip, SYM]
-- The last step is the self-naming link, proved via  parse_roundtrip_term  (a
-- Deriv -- NOT a definitional reduction):  the description slot  parse (linTop
-- x)  equals  codeTerm x , so  pi*  witnesses the atom's SECOND conjunct at the
-- canonical  (Flin* = linTop x, pi* = piStar x) .

piStar : Term -> Term
piStar x = encode (axRefl x)

-- the SECOND conjunct of  atomForm  at  (linTop x, piStar x) :
--   thmT proves the naming equation  g = x  via  pi* .
dSecondConjunct :
  (x : Term) ->
  Deriv (eqF (ap1 thmT (piStar x))
             (nameEqCode (linTop x) x))
dSecondConjunct x =
  ruleTrans (thmT_complete_rec (axRefl x)) (ruleSym (nameEq_roundtrip x x))

------------------------------------------------------------------------
-- SECTION 4.  compress_canonical -- the  dPos  argument of chaitin_thm.
--
-- The KEY simplification (vs the thm13/num representability route): the atom's
-- second conjunct is ITSELF an object equation that  dSecondConjunct  already
-- DERIVES, and the first conjunct  (lenR (linTop x) <= ell)  is a Σ₀ fact T
-- proves whenever the canonical name fits the budget.  So we build the OBJECT
-- proof of the closed atom by  andIntro , and necessitate the WHOLE
-- conjunction once with  thmT_complete_rec  -- no  num<->codeTerm  bridge.
--
-- The length premise  dLen : Deriv (leq (lenR (linTop x)) ell)  is the genuine
-- "the canonical name fits": for  x = chaitinSearch <ell> ,  lenR (linTop x) =
-- const + O(log ell) <= ell  (SPIKE-KR-B), a true Σ₀ fact dischargeable by
-- Σ₀-completeness when  ell  is pinned (the same status as chaitin_thm's
-- (FIT) premise).  Taking it as an argument is NOT a weakening -- it is the
-- length condition, discharged concretely in KR-D.

-- the object proof of the closed canonical atom  atomFormAt ell (linTop x)
-- (piStar x) x  =  (lenR (linTop x) <= ell) AND (naming biconditional via pi*).
compressProof :
  (ell x : Term) ->
  Deriv (leq (ap1 lenR (linTop x)) ell) ->
  Deriv (atomFormAt ell (linTop x) (piStar x) x)
compressProof ell x dLen =
  andIntro (leq (ap1 lenR (linTop x)) ell)
           (eqF (ap1 thmT (piStar x)) (nameEqCode (linTop x) x))
           dLen (dSecondConjunct x)

-- the canonical proof code of compressibility.
cPosCanonical :
  (ell x : Term) -> Deriv (leq (ap1 lenR (linTop x)) ell) -> Term
cPosCanonical ell x dLen = encode (compressProof ell x dLen)

-- compress_canonical (dPos):  thmT proves the closed canonical atom of  x .
dPos :
  (ell x : Term) (dLen : Deriv (leq (ap1 lenR (linTop x)) ell)) ->
  Deriv (eqF (ap1 thmT (cPosCanonical ell x dLen))
             (codeFormula (atomFormAt ell (linTop x) (piStar x) x)))
dPos ell x dLen = thmT_complete_rec (compressProof ell x dLen)

------------------------------------------------------------------------
-- SECTION 5.  chaitinBarrierFinish -- the Chaitin barrier (chaitin_thm) for
-- the canonical SELF-NAMED subject, built CONCRETELY: compress_canonical
-- (dPos) + the D1 axExFalso (dExFGen) + Stage 3 (two encoded_mp + Con +
-- axExFalso) all REAL.  The ONLY abstract input is  dNeg  -- "thmT proves the
-- closed atom is FALSE" -- which is precisely the bounded search's output
-- (KR-B:  hit/out/enum/bridge  +  search_settles ).
--
-- This realises chaitin_thm's Stages 2-3 at the CLOSED atom of the self-named
-- x (the form the de-abstracted chaitin_thm uses: the bridge's OPEN ¬DefWit is
-- thmT_at_sb-instantiated to this closed ¬atom before the encoded_mp's).  So
-- the Chaitin barrier closes with the real KR-A pieces, modulo only the search.

chaitinBarrierFinish :
  Deriv ConSchema ->
  (ell x : Term) ->
  Deriv (leq (ap1 lenR (linTop x)) ell) ->            -- the canonical name fits
  (pNeg : Term) ->
  Deriv (eqF (ap1 thmT pNeg)                           -- the search's output:
             (codeFormula (neg (atomFormAt ell (linTop x) (piStar x) x)))) ->
  Deriv falseF
chaitinBarrierFinish con ell x dLen pNeg dNeg =
  let A : Formula
      A = atomFormAt ell (linTop x) (piStar x) x
      cPos : Term
      cPos = cPosCanonical ell x dLen
      cExF : Term
      cExF = encode (axExFalso A falseF)
      consImp : Term                                   -- code of  (neg A -> false)
      consImp = cImp (codeFormula (neg A)) codeFalse
      -- thmT proves  (neg A -> false)   [MP of dExFGen, dPos].
      mp1 : Deriv (eqF (ap1 thmT (cmp cExF cPos)) consImp)
      mp1 = encoded_mp cExF cPos (codeFormula A) consImp
              (dExFGen A) (dPos ell x dLen)
      -- thmT proves  false              [MP of mp1, dNeg].
      finalProof : Term
      finalProof = cmp (cmp cExF cPos) pNeg
      mp2 : Deriv (eqF (ap1 thmT finalProof) codeFalse)
      mp2 = encoded_mp (cmp cExF cPos) pNeg (codeFormula (neg A)) codeFalse mp1 dNeg
      -- Con refutes it.
      con_inst : Deriv (neg (eqF (ap1 thmT finalProof) codeFalse))
      con_inst = ruleInst zero finalProof con
  in mp (mp (axExFalso (eqF (ap1 thmT finalProof) codeFalse) falseF) mp2) con_inst
