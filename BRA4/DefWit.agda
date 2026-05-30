{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.DefWit -- the Kritchman-Raz definability layer (Phase KR-A), the
-- definitional core that  SpikeChaitin.Search  and the counting abstract:
-- the open DefWit atom  atomForm , its negation  Incompressible , and the
-- object code-builders for the formula codes that  thmT  reads.
--
-- NAME FORMAT (refines SPIKE-KR-NAME-FORMAT-DECISION.md to the SHIPPED
-- round-trip).  The decision said names are linearized FORMULAS, parsed by
-- parse : Fun1  to a tree FORMULA code.  But the shipped  parse  +
-- ParseRoundtrip give a TERM round-trip only --
--
--   parse_roundtrip_term :  parse (linTop t) = codeTerm t
--
-- and a formula code  codeFormula F  is NOT in the image of  codeTerm
-- (its top tag is  tag_eq/neg/imp , never  tag_var/ap1/ap2 ).  So the
-- buildable, shipped-infrastructure-compatible reading is TERM-NAMES:
--
--   * a "name"  Flin  is the linearization  linTop g  of a TERM  g
--     (a description like  chaitinSearch(ell) );  parse Flin = codeTerm g .
--   * the named formula is  v0 = g  (code  cEqTm cV0 (parse Flin) );
--   * x  is compressible-by-Flin iff a proof  pi  witnesses  thmT pi =
--     code of  ((v0 = g) <-> (v0 = x))  AND  lenR Flin <= ell .
--
-- This is faithful Kolmogorov complexity (terms-as-programs): a SHORT term
-- g  (lenR (linTop g) <= ell , e.g.  chaitinSearch(ell) ) may name a HUGE
-- x  via a LONG proof  pi  -- only the term is length-bounded, so the
-- paradox does NOT dissolve (the rejected moves in the name-format
-- decision both bounded the proof or used literal numerals).  lenR over the
-- right-recursive  linTop g  is faithful (counts every symbol), so the
-- length-<=ell name set is finite -- the property the KR-C pigeonhole needs.
--
-- Connectives.  The Formula layer has only  atomic / neg / imp , so  And /
-- Iff  are the standard neg-imp encodings (matched by the object builders
-- cAnd / cIff  so that  codeFormula (fAnd P Q) = cAnd (codeFormula P)
-- (codeFormula Q)  holds DEFINITIONALLY).

module BRA4.DefWit where

open import BRA4.Base
open import BRA4.Tags using ( tag_eq ; tag_neg ; tag_imp )
open import BRA4.Code using ( codeTerm ; codeFormula ; codeFalse ; falseF )
open import BRA4.ThmT using ( thmT )
open import BRA4.LenR using ( lenR )
open import BRA4.Parse using ( parse )
open import BRA4.ParseRoundtrip using ( linTop ; parse_roundtrip_term )
open import BRA4.Encode using ( encode )
open import BRA4.ThmTCompleteRec using ( thmT_complete_rec )

open import BRA3.ChurchLeq using ( leq )
open import BRA3.Contrapositive using ( axExFalso )

------------------------------------------------------------------------
-- SECTION 1.  Object code-builders.
--
-- These mirror  codeFormula  on the three Formula shapes so that codes
-- built from object terms (e.g.  ap1 parse Flin ) interoperate with codes
-- built by  codeFormula  on meta formulas.  cAnd / cIff  follow the
-- neg/imp encodings used by  fAnd / fIff  below.

-- code of an atomic equation  a = b , from term-codes  a , b .
--   (= codeFormula (atomic (eqn a' b'))  when  a = codeTerm a' , b = codeTerm b').
cEqTm : Term -> Term -> Term
cEqTm a b = ap2 Pair (natCode tag_eq) (ap2 Pair a b)

-- code of  neg P , from the code of  P .
cNeg : Term -> Term
cNeg c = ap2 Pair (natCode tag_neg) c

-- code of  imp P Q , from the codes of  P , Q .
cImp : Term -> Term -> Term
cImp a b = ap2 Pair (natCode tag_imp) (ap2 Pair a b)

-- code of  And P Q  (= neg (imp P (neg Q))).
cAnd : Term -> Term -> Term
cAnd a b = cNeg (cImp a (cNeg b))

-- code of  Iff P Q  (= And (imp P Q) (imp Q P)).
cIff : Term -> Term -> Term
cIff a b = cAnd (cImp a b) (cImp b a)

-- code of the variable  v0  (closed: built from natCodes only).
cV0 : Term
cV0 = codeTerm (var zero)

------------------------------------------------------------------------
-- SECTION 2.  Meta formula-builders for And / Iff over the neg/imp core.
--
-- Chosen so that  codeFormula  commutes with the object builders:
--   codeFormula (fAnd P Q) = cAnd (codeFormula P) (codeFormula Q)   (definitional)
--   codeFormula (fIff P Q) = cIff (codeFormula P) (codeFormula Q)   (definitional)

fAnd : Formula -> Formula -> Formula
fAnd p q = neg (imp p (neg q))

fIff : Formula -> Formula -> Formula
fIff p q = fAnd (imp p q) (imp q p)

------------------------------------------------------------------------
-- SECTION 3.  The open DefWit atom and Incompressible.
--
-- Free object variables (open Pi_1 form):
--   var 1  = Flin  (the linearized term-name)
--   var 2  = pi    (the proof code)
-- The subject  x  is plugged into the atom; the length budget  ell  is a
-- Term parameter (a Bin numeral in use).  No  var 0  is free: the named
-- formula's  v0  rides as the CLOSED code  cV0  inside the formula code.

vFlin : Term
vFlin = var (suc zero)

vPi : Term
vPi = var (suc (suc zero))

-- code of the named formula  "v0 = (term whose code is  parse Flin)" .
namedCode : Term -> Term
namedCode flin = cEqTm cV0 (ap1 parse flin)

-- code of the subject formula  "v0 = x" .
subjCode : Term -> Term
subjCode x = cEqTm cV0 (codeTerm x)

-- nameEqCode flin x  : code of the TERM-EQUALITY naming formula  "g = x" , where
-- g  is the description term named by  flin  (parse flin = codeTerm g).  This is
-- the operative naming notion (simpler than the biconditional "(v0=g)<->(v0=x)":
-- the subject  x  occurs ONCE, and self-naming  g = x  is proved by  axRefl ),
-- equivalent for con_inj  (g=x AND g=x' => x=x').
nameEqCode : Term -> Term -> Term
nameEqCode flin x = cEqTm (ap1 parse flin) (codeTerm x)

-- atomFormAt ell flin pi x  : the DefWit atom with the name / proof slots
-- FILLED by  flin / pi  (the closed-instance form  compress_canonical builds;
-- the surrounding chaitin_thm threads the open->closed link via thmT_at_sb).
--   (lenR flin <= ell)  AND  (thmT pi = code of  (g = x))  [g named by flin] .
atomFormAt : Term -> Term -> Term -> Term -> Formula
atomFormAt ell flin pi x =
  fAnd (leq (ap1 lenR flin) ell)
       (eqF (ap1 thmT pi) (nameEqCode flin x))

-- atomForm ell x  : the open DefWit atom for subject  x  at budget  ell
-- (name = vFlin = var 1 , proof = vPi = var 2 , both free).
atomForm : Term -> Term -> Formula
atomForm ell x = atomFormAt ell vFlin vPi x

-- Incompressible ell x  = "K(x) > ell"  = the open Pi_1 negation.
Incompressible : Term -> Term -> Formula
Incompressible ell x = neg (atomForm ell x)

------------------------------------------------------------------------
-- SECTION 4.  codeFormula commutes with the object builders.
--
-- These hold DEFINITIONALLY (the object builders were chosen to mirror
-- codeFormula on neg/imp); recorded as machine-checked documentation and
-- reused by  compress_canonical  to relate thmT-provability of  fAnd / fIff
-- to provability of the constituents.

codeFormula_fAnd :
  (p q : Formula) ->
  Eq (codeFormula (fAnd p q)) (cAnd (codeFormula p) (codeFormula q))
codeFormula_fAnd p q = refl

codeFormula_fIff :
  (p q : Formula) ->
  Eq (codeFormula (fIff p q)) (cIff (codeFormula p) (codeFormula q))
codeFormula_fIff p q = refl

------------------------------------------------------------------------
-- SECTION 5.  The parse round-trip bridges (the term-name link).
--
-- These connect the SYNTACTIC name  linTop g  (the right-recursive
-- linearization of a description term  g ) to the SEMANTIC formula code
-- that  thmT  reads, using the shipped  parse_roundtrip_term .  They are
-- exactly what  compress_canonical  needs: the canonical name of  yhat  is
-- linTop g  for a short term  g  (e.g.  g = chaitinSearch <ell> ), and the
-- atom's named-formula slot must provably equal  codeFormula (v0 = g) .

-- congruence of  cIff  in its first argument.
cIffCongL :
  (a a' b : Term) -> Deriv (eqF a a') ->
  Deriv (eqF (cIff a b) (cIff a' b))
cIffCongL a a' b e =
  let eImpAB : Deriv (eqF (cImp a b) (cImp a' b))
      eImpAB = congR Pair (natCode tag_imp) (congL Pair b e)
      eNegImpBA : Deriv (eqF (cNeg (cImp b a)) (cNeg (cImp b a')))
      eNegImpBA = congR Pair (natCode tag_neg)
                    (congR Pair (natCode tag_imp) (congR Pair b e))
      inner : Deriv (eqF (ap2 Pair (cImp a b) (cNeg (cImp b a)))
                         (ap2 Pair (cImp a' b) (cNeg (cImp b a'))))
      inner = ruleTrans (congL Pair (cNeg (cImp b a)) eImpAB)
                        (congR Pair (cImp a' b) eNegImpBA)
  in congR Pair (natCode tag_neg)
       (congR Pair (natCode tag_imp) inner)

-- the named-formula code of  linTop g  equals  codeFormula (v0 = g) .
namedCode_roundtrip :
  (g : Term) ->
  Deriv (eqF (namedCode (linTop g)) (codeFormula (eqF (var zero) g)))
namedCode_roundtrip g =
  congR Pair (natCode tag_eq) (congR Pair cV0 (parse_roundtrip_term g))

-- the iff-code of the canonical name and subject equals  codeFormula
-- (fIff (v0 = g) (v0 = x)) :  the full named-defining-formula bridge.
atomIff_roundtrip :
  (g x : Term) ->
  Deriv (eqF (cIff (namedCode (linTop g)) (subjCode x))
             (codeFormula (fIff (eqF (var zero) g) (eqF (var zero) x))))
atomIff_roundtrip g x =
  cIffCongL (namedCode (linTop g)) (codeFormula (eqF (var zero) g)) (subjCode x)
    (namedCode_roundtrip g)

-- the term-equality naming code of the canonical name  linTop g  equals
-- codeFormula (g = x) :  the bridge  compress_canonical / the search use for
-- the term-equality atom (proved via parse_roundtrip_term, not by reduction).
nameEq_roundtrip :
  (g x : Term) ->
  Deriv (eqF (nameEqCode (linTop g) x) (codeFormula (eqF g x)))
nameEq_roundtrip g x =
  congR Pair (natCode tag_eq) (congL Pair (codeTerm x) (parse_roundtrip_term g))

------------------------------------------------------------------------
-- SECTION 6.  dExF -- the D1 necessitation of  axExFalso  on the atom.
--
-- This is the  chaitin_thm  Stage-2 argument  dExF  (NEXT-SESSION-KR-A
-- step 4 / SpikeChaitin chaitin_thm).  It is NOT a new obligation: the
-- shipped recursive necessitation  thmT_complete_rec  applied to the
-- shipped derived rule  axExFalso  delivers it directly, for ANY  atomForm
-- shape (open or closed).  The conclusion is stated in the spike's  cImp
-- form;  codeFormula  on the  imp/imp/neg/falseF  tree reduces to it
-- definitionally (codeFalse = codeFormula falseF).

-- general form: the D1 necessitation of  axExFalso  on ANY formula  A
-- (used by compress_canonical at the CLOSED atom; open A also fine).
dExFGen :
  (A : Formula) ->
  Deriv (eqF (ap1 thmT (encode (axExFalso A falseF)))
             (cImp (codeFormula A) (cImp (codeFormula (neg A)) codeFalse)))
dExFGen A = thmT_complete_rec (axExFalso A falseF)

cExF : Term -> Term -> Term
cExF ell x = encode (axExFalso (atomForm ell x) falseF)

dExF :
  (ell x : Term) ->
  Deriv (eqF (ap1 thmT (cExF ell x))
             (cImp (codeFormula (atomForm ell x))
                   (cImp (codeFormula (neg (atomForm ell x))) codeFalse)))
dExF ell x = dExFGen (atomForm ell x)
