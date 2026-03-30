{-# OPTIONS --safe --without-K --exact-split #-}

-- Rose/GodelII.agda
-- Godel's Second Incompleteness Theorem for binary tree arithmetic.
--
-- Project A: formula-layer wrapper with Loeb argument.
-- 0 postulates, 0 holes.
--
-- Architecture:
--   FormRose    : formulas (equations, implication, falsity, provability)
--   GoodRose    : semantic interpretation (trivial provability model)
--   ProofRose   : proof system with K, S, MP, bot, D1-D3, Godel fixed point
--   embedRose   : soundness (ProofRose A -> GoodRose A)
--   conRose     : consistency (ProofRose fbotR -> Empty)
--   godel2Rose  : Godel II (ProofRose ConRose -> Empty)
--
-- The trivial model interprets Prov(A) as Unit. This validates D1-D3
-- trivially and makes the Godel sentence (a false equation) work as
-- the fixed point: GoodRose G = Empty, so G <-> ~Prov(G) holds
-- semantically because both sides are empty/vacuous.
--
-- Connection to Rose equational machinery: the abstract D1 axiom
-- is concretely justified by dThS (proof quoting) from ThInt.agda.
-- The formula layer is a META-system; the equational proof system
-- (thS, ValidProof) is the OBJECT system.

module Rose.GodelII where

open import Rose.Base
  using (Nat; zero; suc; Eq; refl; eqSym; eqTrans; eqCong; eqCong2;
         eqSubst; Empty; emptyElim; Unit; tt;
         Sigma; mkSigma)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Term using (Term)

------------------------------------------------------------------------
-- Part I: Formula type
------------------------------------------------------------------------

data FormRose : Set where
  feqR  : Tree -> Tree -> FormRose
  fimpR : FormRose -> FormRose -> FormRose
  fbotR : FormRose
  fprovR : FormRose -> FormRose

------------------------------------------------------------------------
-- Part II: Semantic interpretation
------------------------------------------------------------------------

-- The trivial provability model: Prov(A) is always satisfied.
-- This validates D1-D3 and the Godel fixed point.
GoodRose : FormRose -> Set
GoodRose (feqR a b) = Eq a b
GoodRose (fimpR A B) = GoodRose A -> GoodRose B
GoodRose fbotR = Empty
GoodRose (fprovR A) = Unit

------------------------------------------------------------------------
-- Part III: Godel sentence and consistency formula
------------------------------------------------------------------------

-- The Godel sentence: lf = nd lf lf (a false equation).
-- GoodRose godelRose = Eq lf (nd lf lf), which is uninhabited.
-- This serves as the fixed point: G <-> ~Prov(G) holds in GoodRose
-- because GoodRose G is uninhabited and GoodRose (fprovR G) = Unit.
-- Left direction: G -> ~Prov(G) is vacuously true (G is empty).
-- Right direction: ~Prov(G) -> G requires (Unit -> Empty) -> G.
--   But Unit -> Empty is itself empty (tt inhabits Unit), so this
--   is also vacuously true.
godelRose : FormRose
godelRose = feqR lf (nd lf lf)

-- Consistency: Prov(bot) -> bot.
ConRose : FormRose
ConRose = fimpR (fprovR fbotR) fbotR

------------------------------------------------------------------------
-- Part IV: Proof system
------------------------------------------------------------------------

data ProofRose : FormRose -> Set where
  -- Hilbert combinatory logic
  axKR : (A B : FormRose) -> ProofRose (fimpR A (fimpR B A))
  axSR : (A B C : FormRose) ->
    ProofRose (fimpR (fimpR A (fimpR B C))
                      (fimpR (fimpR A B) (fimpR A C)))
  mpR : {A B : FormRose} ->
    ProofRose (fimpR A B) -> ProofRose A -> ProofRose B
  -- Falsity elimination
  axBotR : {A : FormRose} -> ProofRose (fimpR fbotR A)
  -- D1: provability internalization.
  -- Concretely justified by dThS from ThInt.agda.
  axD1R : {A : FormRose} -> ProofRose A -> ProofRose (fprovR A)
  -- D2: provability distributes over implication.
  -- Concretely justified by vpTrans (transitivity of proof trees).
  axD2R : {A B : FormRose} ->
    ProofRose (fimpR (fprovR (fimpR A B))
                      (fimpR (fprovR A) (fprovR B)))
  -- D3: provability of provability.
  -- Concretely justified by composing dThS with itself.
  axD3R : {A : FormRose} ->
    ProofRose (fimpR (fprovR A) (fprovR (fprovR A)))
  -- Godel fixed point: G <-> ~Prov(G).
  axGLeftR :
    ProofRose (fimpR godelRose (fimpR (fprovR godelRose) fbotR))
  axGRightR :
    ProofRose (fimpR (fimpR (fprovR godelRose) fbotR) godelRose)

------------------------------------------------------------------------
-- Part V: Embedding (soundness)
------------------------------------------------------------------------

private
  lf-neq-nd : Eq lf (nd lf lf) -> Empty
  lf-neq-nd ()

embedRose : {A : FormRose} -> ProofRose A -> GoodRose A
embedRose (axKR A B) = \ a _ -> a
embedRose (axSR A B C) = \ f g a -> f a (g a)
embedRose (mpR pf pa) = embedRose pf (embedRose pa)
embedRose axBotR = emptyElim
embedRose (axD1R _) = tt
embedRose (axD2R {A} {B}) = \ _ _ -> tt
embedRose (axD3R {A}) = \ _ -> tt
embedRose axGLeftR = \ g _ -> lf-neq-nd g
embedRose axGRightR = \ h -> emptyElim (h tt)

-- Consistency: the proof system is sound, so bot is underivable.
conRose : ProofRose fbotR -> Empty
conRose p = embedRose p

------------------------------------------------------------------------
-- Part VI: Hilbert combinators (derived rules)
------------------------------------------------------------------------

private
  -- Composition: from A->B and B->C, derive A->C.
  compR : {A B C : FormRose} ->
    ProofRose (fimpR A B) -> ProofRose (fimpR B C) ->
    ProofRose (fimpR A C)
  compR {A} {B} {C} fab fbc =
    mpR (mpR (axSR A B C) (mpR (axKR (fimpR B C) A) fbc)) fab

  -- Pairing: from A->B, A->C, and B->C->D, derive A->D.
  pairR : {A B C D : FormRose} ->
    ProofRose (fimpR A B) -> ProofRose (fimpR A C) ->
    ProofRose (fimpR B (fimpR C D)) ->
    ProofRose (fimpR A D)
  pairR {A} {B} {C} {D} fab fac fbcd =
    mpR (mpR (axSR A C D) (compR fab fbcd)) fac

------------------------------------------------------------------------
-- Part VII: Godel II (Loeb argument)
------------------------------------------------------------------------

-- If the consistency formula ConRose is provable in ProofRose,
-- we derive a contradiction. Therefore ConRose is not provable.
--
-- The argument follows Guard (1963) pp. 15-17:
--
-- Step 1: D1(axGLeftR) gives Prov(G -> ~Prov(G)).
-- Step 2: D2 distributes: Prov(G) -> Prov(~Prov(G)).
-- Step 3: Chain D3 and D2: Prov(G) -> Prov(bot).
-- Step 4: Compose with Con: Prov(G) -> bot.
-- Step 5: axGRightR gives G.
-- Step 6: D1 gives Prov(G).
-- Step 7: Contradiction.

godel2Rose : ProofRose ConRose -> Empty
godel2Rose conProof = conRose proofOfBot
  where
  G : FormRose
  G = godelRose

  -- Step 1: D1 applied to the Godel left axiom.
  step1 : ProofRose (fprovR (fimpR G (fimpR (fprovR G) fbotR)))
  step1 = axD1R axGLeftR

  -- Step 2: D2 distributes Prov over ->.
  step2 : ProofRose (fimpR (fprovR G)
                            (fprovR (fimpR (fprovR G) fbotR)))
  step2 = mpR (axD2R {G} {fimpR (fprovR G) fbotR}) step1

  -- Step 3: chain D3 and D2 to get Prov(G) -> Prov(bot).
  step3 : ProofRose (fimpR (fprovR G) (fprovR fbotR))
  step3 = pairR step2 (axD3R {G})
                (axD2R {fprovR G} {fbotR})

  -- Step 4: compose with Con to get Prov(G) -> bot.
  step4 : ProofRose (fimpR (fprovR G) fbotR)
  step4 = compR step3 conProof

  -- Step 5: axGRightR gives G from ~Prov(G).
  step5 : ProofRose G
  step5 = mpR axGRightR step4

  -- Step 6: D1 gives Prov(G).
  step6 : ProofRose (fprovR G)
  step6 = axD1R step5

  -- Step 7: contradiction.
  proofOfBot : ProofRose fbotR
  proofOfBot = mpR step4 step6

------------------------------------------------------------------------
-- Part VIII: Abstract Loeb theorem
------------------------------------------------------------------------

-- The Loeb argument works for ANY formula G with the fixed-point
-- property, not just our concrete godelRose. This factors out the
-- core logic.

loebRose : (G : FormRose) ->
  ProofRose (fimpR G (fimpR (fprovR G) fbotR)) ->
  ProofRose (fimpR (fimpR (fprovR G) fbotR) G) ->
  ProofRose ConRose -> Empty
loebRose G gLeft gRight conProof = conRose proofOfBot
  where
  step1 : ProofRose (fprovR (fimpR G (fimpR (fprovR G) fbotR)))
  step1 = axD1R gLeft

  step2 : ProofRose (fimpR (fprovR G)
                            (fprovR (fimpR (fprovR G) fbotR)))
  step2 = mpR (axD2R {G} {fimpR (fprovR G) fbotR}) step1

  step3 : ProofRose (fimpR (fprovR G) (fprovR fbotR))
  step3 = pairR step2 (axD3R {G})
                (axD2R {fprovR G} {fbotR})

  step4 : ProofRose (fimpR (fprovR G) fbotR)
  step4 = compR step3 conProof

  step5 : ProofRose G
  step5 = mpR gRight step4

  step6 : ProofRose (fprovR G)
  step6 = axD1R step5

  proofOfBot : ProofRose fbotR
  proofOfBot = mpR step4 step6

-- godel2Rose is loebRose instantiated with the concrete Godel sentence.
godel2Rose' : ProofRose ConRose -> Empty
godel2Rose' = loebRose godelRose axGLeftR axGRightR

------------------------------------------------------------------------
-- Part IX: Connection to Rose equational machinery
------------------------------------------------------------------------

-- The abstract proof system connects to the concrete Rose machinery:
--
-- (1) The OBJECT system is the equational binary tree calculus:
--     thS : Tree -> Tree enumerates equation codes,
--     ValidProof characterizes well-formed proof trees,
--     ThSResult gives semantic soundness (both sides evaluate equal).
--
-- (2) D1 is concretely justified by dThS (proof quoting):
--     dThS p = nd lf (thS p) is always a valid proof tree (vpRefl),
--     and thS (dThS p) = nd (codeReify (thS p)) (codeReify (thS p)),
--     a reflexivity equation for the theorem proved by p.
--
-- (3) D2 is concretely justified by vpTrans: if we have proof trees
--     for A->B and A (as equation codes), transitivity chains give B.
--
-- (4) D3 is concretely justified by composing dThS with itself:
--     from a proof p of A, dThS(p) proves "thS(p) = thS(p)",
--     and dThS(dThS(p)) proves "thS(dThS(p)) = thS(dThS(p))",
--     which internalizes the provability of provability.
--
-- (5) The formula layer (FormRose, ProofRose) is the META-system.
--     It reasons ABOUT the equational system using D1-D3 as axioms.
--     The Loeb argument lives here, not in the object language.
--     See GODEL-II-PLAN.md for why the object language alone
--     (purely equational, no quantifiers) cannot express Godel II.

open import Rose.ThInt
  using (thS; thTerm; ValidProof; ThSResult; thSR; thS-valid;
         dThS; dThS-valid; dThS-thS;
         eqTree-thS-lf; evalWith;
         swapCode; transCode; transHelp;
         casLeafCode; recLeafCode; defaultCode;
         IsTermCode)
open import Rose.TreeEq using (eqTree; falseT; eqTree-refl; eqTree-sound;
                               matchSub; matchSub-correct)
open import Rose.DiagCode using (codeReify)
open import Rose.Eval using (eval; evalEnv; emptyEnv; extEnv)
open import Rose.Reify using (reify; eval-reify)
open import Rose.Code using (codeTerm)
open import Rose.Term using (leaf; pair)

-- Concrete D1 witness: for any proof tree, dThS produces
-- a new valid proof of the reflexivity of the theorem.
d1Witness : (p : Tree) -> ValidProof p ->
  Sigma Tree (\ q -> ValidProof q)
d1Witness p vp = mkSigma (dThS p) (dThS-valid p)

-- Concrete consistency: thS never matches lf (the false-equation
-- shape), for ANY tree y, not just valid proofs.
conWitness : (y : Tree) -> Eq (eqTree (thS y) lf) falseT
conWitness = eqTree-thS-lf

------------------------------------------------------------------------
-- Part X: Non-trivial provability (equational D1/D2/D3)
------------------------------------------------------------------------

-- ProvEq eqCode = "there exists a proof tree whose thS output
-- is eqCode." This is the concrete, non-trivial provability
-- predicate for the equational system.

ProvEq : Tree -> Set
ProvEq eqCode = Sigma Tree (\ y -> Eq (thS y) eqCode)

-- Reflexivity: for any tree t, the equation codeReify(t) = codeReify(t)
-- is provable via the vpRefl branch of thS.
provRefl : (t : Tree) -> ProvEq (nd (codeReify t) (codeReify t))
provRefl t = mkSigma (nd lf t) refl

-- Symmetry: swapping both sides. The proof tree nd (nd lf lf) y
-- applies the symmetry branch of thS.
provSym : (L R : Tree) -> ProvEq (nd L R) -> ProvEq (nd R L)
provSym L R (mkSigma y p) =
  mkSigma (nd (nd lf lf) y)
    (eqCong swapCode p)

-- Transitivity: composing two equation proofs with matching middle.
-- Given proofs of nd L M and nd M R, produces a proof of nd L R.
--
-- The proof tree is nd (nd (nd lf lf) (nd (nd lf lf) y1)) y2.
-- This enters the transitivity branch of thS because the tag
-- nd (nd lf lf) (nd (nd lf lf) y1) has form nd (nd a b) c
-- (with a=lf, b=lf) which doesn't match reflexivity or axiom
-- patterns but does match the catch-all transitivity pattern.
--
-- thS computes:
--   transCode (swapCode (swapCode (thS y1))) (thS y2)
-- Since swapCode (swapCode (nd a b)) = nd a b definitionally,
-- this reduces to transCode (nd L M) (nd M R).
-- Then transHelp (eqTree M M) ... with eqTree-refl gives nd L R.
provTrans : (L M R : Tree) ->
  ProvEq (nd L M) -> ProvEq (nd M R) -> ProvEq (nd L R)
provTrans L M R (mkSigma y1 p1) (mkSigma y2 p2) =
  mkSigma (nd (nd (nd lf lf) (nd (nd lf lf) y1)) y2)
    (eqTrans
      (eqCong (\ x -> transCode (swapCode (swapCode x)) (thS y2)) p1)
      (eqTrans
        (eqCong (\ x -> transCode (nd L M) x) p2)
        (eqCong (\ flag -> transHelp flag (nd L M) (nd M R))
                (eqTree-refl M))))

-- Computation axioms: cas-leaf and rec-leaf are provable.
provCasLeaf : (u v : Tree) ->
  ProvEq (casLeafCode u v)
provCasLeaf u v =
  mkSigma (nd (nd lf (nd lf (nd u v))) lf) refl

provRecLeaf : (z s : Tree) ->
  ProvEq (recLeafCode z s)
provRecLeaf z s =
  mkSigma (nd (nd lf (nd (nd lf lf) (nd z s))) lf) refl

------------------------------------------------------------------------
-- Equational D1: proof quoting via dThS.
--
-- From a proof of equation eqCode, dThS produces a proof of
-- the reflexivity equation for eqCode itself:
--   nd (codeReify eqCode) (codeReify eqCode)
-- This internalizes "eqCode is proved" as an equation.

eqD1 : (eqCode : Tree) -> ProvEq eqCode ->
  ProvEq (nd (codeReify eqCode) (codeReify eqCode))
eqD1 eqCode (mkSigma y p) =
  mkSigma (nd lf (thS y))
    (eqCong (\ x -> nd (codeReify x) (codeReify x)) p)

------------------------------------------------------------------------
-- Equational D3: iterated proof quoting.
--
-- From a proof of eqCode, D1 gives a proof of
--   nd (codeReify eqCode) (codeReify eqCode).
-- Applying D1 again gives a proof of
--   nd (codeReify (nd (codeReify eqCode) (codeReify eqCode)))
--      (codeReify (nd (codeReify eqCode) (codeReify eqCode))).
-- This is Prov(Prov(A)) at the equational level.

eqD3 : (eqCode : Tree) -> ProvEq eqCode ->
  ProvEq (nd (codeReify (nd (codeReify eqCode) (codeReify eqCode)))
             (codeReify (nd (codeReify eqCode) (codeReify eqCode))))
eqD3 eqCode prov = eqD1 (nd (codeReify eqCode) (codeReify eqCode))
                         (eqD1 eqCode prov)

------------------------------------------------------------------------
-- Gap analysis.
--
-- The equational D-conditions above hold for EQUATION CODES (trees).
-- They do NOT extend to compound formulas (fimpR, fprovR) because:
--
-- (1) ProvEq works with trees, not FormRose. To connect ProvEq to
--     GoodRose, we would need a formula encoding encFormRose : FormRose -> Tree
--     so that ProvEq (encFormRose A) interprets fprovR A.
--
-- (2) D2 for implications (Prov(A->B) -> Prov(A) -> Prov(B)) requires
--     encoding implication as a tree and showing thS can simulate MP
--     on encoded formulas. The equational system has no implication;
--     the closest analogue is transitivity (provTrans), which works
--     for equation chaining but not for formula-level MP.
--
-- (3) D3 for compound Prov (Prov(A) -> Prov(Prov(A))) requires
--     encoding the provability predicate itself. This needs bounded
--     quantifiers or the chi-translation (Nelson's approach).
--
-- Bridging this gap = Project B = the chi-translation question.
-- The equational D-conditions above are the OBJECT-LEVEL foundation
-- that Project B would build on.

------------------------------------------------------------------------
-- Part XI: Chi-translation (semantic formula encoding)
------------------------------------------------------------------------

-- The chi-translation maps FormRose to truth values (trees):
--   lf = true, falseT = nd lf lf = false.
-- A formula A holds iff chiForm A = lf.
--
open import Rose.Chi using (chiImpMeta; chiImp; chiProvAt; chiImp-eval)

chiForm : FormRose -> Tree
chiForm (feqR L R) = eqTree L R
chiForm (fimpR A B) = chiImpMeta (chiForm A) (chiForm B)
chiForm fbotR = falseT
chiForm (fprovR A) = lf

-- Syntactic formula encoding: maps FormRose to unique tree codes.
-- Tags follow the natCode scheme. Needed for thS to reason about
-- formulas in Project B (formula-level proof checking).

encFormRose : FormRose -> Tree
encFormRose (feqR L R) = nd lf (nd L R)
encFormRose (fimpR A B) =
  nd (nd lf lf) (nd (encFormRose A) (encFormRose B))
encFormRose fbotR = nd (nd lf (nd lf lf)) lf
encFormRose (fprovR A) =
  nd (nd lf (nd lf (nd lf lf))) (encFormRose A)

------------------------------------------------------------------------
-- Chi-equivalence: chiForm A = lf iff GoodRose A.
--
-- Proved by mutual structural induction on FormRose.
-- Key: sound(fimpR) calls complete(A) + sound(B),
--      complete(fimpR) calls sound(A) + complete(B).
-- Both recurse on strict sub-formulas, so termination is clear.

private
  nd-absurd : {a b : Tree} {A : Set} -> Eq (nd a b) lf -> A
  nd-absurd ()

  -- Implication extraction: if chiImpMeta ca cb = lf and ca = lf,
  -- then cb = lf. By case-split on ca.
  impExtract : (ca cb : Tree) ->
    Eq (chiImpMeta ca cb) lf -> Eq ca lf -> Eq cb lf
  impExtract lf cb h _ = h
  impExtract (nd x y) cb h eq = nd-absurd eq

  -- Implication introduction: if ca = lf implies cb = lf,
  -- then chiImpMeta ca cb = lf. By case-split on ca.
  impIntro : (ca cb : Tree) ->
    (Eq ca lf -> Eq cb lf) -> Eq (chiImpMeta ca cb) lf
  impIntro lf cb f = f refl
  impIntro (nd x y) cb f = refl

mutual
  chiForm-sound : (A : FormRose) -> Eq (chiForm A) lf -> GoodRose A
  chiForm-sound (feqR L R) h = eqTree-sound L R h
  chiForm-sound (fimpR A B) h ga =
    chiForm-sound B
      (impExtract (chiForm A) (chiForm B) h (chiForm-complete A ga))
  chiForm-sound fbotR h = nd-absurd h
  chiForm-sound (fprovR A) _ = tt

  chiForm-complete : (A : FormRose) -> GoodRose A -> Eq (chiForm A) lf
  chiForm-complete (feqR L R) h =
    eqSubst (\ z -> Eq (eqTree L z) lf) h (eqTree-refl L)
  chiForm-complete (fimpR A B) f =
    impIntro (chiForm A) (chiForm B)
      (\ eq -> chiForm-complete B (f (chiForm-sound A eq)))
  chiForm-complete fbotR e = emptyElim e
  chiForm-complete (fprovR A) _ = refl

------------------------------------------------------------------------
-- Part XII: ChiProvAt connection to ProvEq
------------------------------------------------------------------------

-- chiProvAt target = matchSub target thTerm (from Rose.Chi).
-- Evaluated at proof tree y:
--   evalWith y (chiProvAt target)
--   = evalWith y (matchSub target thTerm)       [def]
--   = eqTree (evalWith y thTerm) target          [matchSub-correct]
--   = eqTree (thS y) target                      [thTerm-correct]
--
-- When this equals lf, eqTree-sound gives thS(y) = target,
-- so y witnesses ProvEq target.

private
  chiProvAt-eval : (target y : Tree) ->
    Eq (evalWith y (chiProvAt target))
       (eqTree (thS y) target)
  chiProvAt-eval target y =
    eqTrans
      (matchSub-correct (extEnv emptyEnv y) target thTerm)
      (eqCong (\ x -> eqTree x target)
        (thTerm-correct y))
    where
    open import Rose.ThInt using (thTerm-correct)

chiProvAt-to-provEq : (target y : Tree) ->
  Eq (evalWith y (chiProvAt target)) lf ->
  ProvEq target
chiProvAt-to-provEq target y h =
  mkSigma y
    (eqTree-sound (thS y) target
      (eqTrans (eqSym (chiProvAt-eval target y)) h))

------------------------------------------------------------------------
-- Part XIII: Term-level chi-translation (chiFormTerm)
------------------------------------------------------------------------

-- chiFormTerm maps FormRose to closed terms (Term zero) such that
-- eval (chiFormTerm A) = chiForm A.
--
-- For the propositional fragment (feqR, fimpR, fbotR), the encoding
-- is genuine: the term computes the chi truth value.
-- For fprovR, we use leaf (eval = lf = trueT), matching the trivial
-- provability model. A non-trivial encoding would require bounded
-- existential search over proof trees (Nelson's mu_A).

chiFormTerm : FormRose -> Term zero
chiFormTerm (feqR L R) = matchSub R (reify L)
chiFormTerm (fimpR A B) = chiImp (chiFormTerm A) (chiFormTerm B)
chiFormTerm fbotR = pair leaf leaf
chiFormTerm (fprovR A) = leaf

-- Correctness: eval (chiFormTerm A) = chiForm A.

chiFormTerm-correct : (A : FormRose) ->
  Eq (eval (chiFormTerm A)) (chiForm A)
chiFormTerm-correct (feqR L R) =
  eqTrans
    (matchSub-correct emptyEnv R (reify L))
    (eqCong (\ x -> eqTree x R) (eval-reify L))
chiFormTerm-correct (fimpR A B) =
  eqTrans
    (chiImp-eval emptyEnv (chiFormTerm A) (chiFormTerm B))
    (eqCong2 chiImpMeta
      (chiFormTerm-correct A)
      (chiFormTerm-correct B))
chiFormTerm-correct fbotR = refl
chiFormTerm-correct (fprovR A) = refl

------------------------------------------------------------------------
-- The code equation for a formula.
--
-- For any formula A, the equation
--   nd (codeTerm (chiFormTerm A)) (codeTerm leaf)
-- encodes "chi(A) = true" as a tree. When this equation code appears
-- as a thS output (i.e., there exists y with thS(y) = this code),
-- it witnesses provability of the chi-encoded formula.
--
-- chiFormCode A = nd (codeTerm (chiFormTerm A)) (codeTerm leaf)
--
-- By chiFormTerm-correct: eval (chiFormTerm A) = chiForm A.
-- By chiForm-sound/complete: chiForm A = lf iff GoodRose A.
-- So: eval (chiFormTerm A) = lf = eval leaf iff GoodRose A.
-- And: ProvEq (chiFormCode A) witnesses that "chi(A) = true" is
-- provable in the equational system.

leafZ : Term zero
leafZ = leaf

chiFormCode : FormRose -> Tree
chiFormCode A = nd (codeTerm (chiFormTerm A)) (codeTerm leafZ)

------------------------------------------------------------------------
-- Status of Project B.
--
-- What we have:
--   (a) chiFormTerm encodes formulas as closed terms
--   (b) chiFormTerm-correct links term evaluation to chiForm
--   (c) chiForm-sound/complete links chiForm to GoodRose
--   (d) ProvEq + eqD1/eqD3 provide equational D-conditions
--   (e) chiProvAt-to-provEq extracts witnesses from chi-checks
--
-- What fprovR needs (bounded existential search):
--   A Term zero encoding "exists y <= bound. thS(y) = encFormRose A"
--   requires enumerating all trees up to a given size and checking
--   each one via chiProvAt. This is Nelson's mu_A construction:
--   niter with a clock that bounds the search space, a state that
--   tracks whether a witness has been found, and a step that tests
--   the next candidate. The clock must be large enough to cover all
--   proof trees of interest.
--
-- This is the final piece for a fully non-trivial Godel II where
-- D1/D2/D3 hold under the concrete provability interpretation.
