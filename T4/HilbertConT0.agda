{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.HilbertConT0 -- the ALTERNATIVE route to meta Con(T0) (attempt3 §14):
-- SEMANTIC SOUNDNESS, with NO cut-elimination and NO sequent calculus at all.
--
-- T0 is modelled DIRECTLY as Guard intends it -- a HILBERT system: closed
-- equational/recursor axiom instances + the classical propositional schemas
-- (K, S, double-negation, ex-falso) + modus ponens.  Consistency follows from a
-- SINGLE structural-induction soundness lemma into the convertibility model:
--
--   [[ a = b ]] := ¬¬ (Conv a b)   (the Σ1 / object-E "joinable"; NOT eval)
--   [[ bot ]]   := Empty
--   [[ p -> q ]]:= [[p]] -> [[q]]
--
--   sound : ThmT0 f -> [[ f ]]          -- one induction; MP is a SOUND rule
--   conT0 : Not (ThmT0 (0 = s0))        -- because Conv 0 (s0) is false (L3)
--
-- The double negation on atoms makes every [[f]] ¬¬-STABLE, which validates the
-- classical schema ((p->bot)->bot)->p constructively.  This file imports ONLY
-- the Church-Rosser convertibility interface (T4.ConvInterface, = L1/L2/L3) and
-- is INDEPENDENT of T4.G3Logic: it demonstrates cut-elimination is dispensable.
--
-- Self-contained, ASCII, --safe --without-K --exact-split, no holes/postulates.

module T4.HilbertConT0 where

import T4.ParReflPres   as PR
import T4.ParStep       as PS
import T4.ParHeadline   as PH
import T4.EqSound       as ES
import T4.ConvInterface as CI

open PR using ( Tm ; ze ; su ; ad )

------------------------------------------------------------------------
-- Minimal logical prelude (independent of G3Logic).

data Empty : Set where

emptyElim : {A : Set} -> Empty -> A
emptyElim ()

Not : Set -> Set
Not A = A -> Empty

pe : PH.Empty -> Empty
pe ()

------------------------------------------------------------------------
-- Formulas of T0: atoms are equations between toy terms.

data Eqn : Set where
  eqn : Tm -> Tm -> Eqn

data Form : Set where
  at  : Eqn -> Form
  bot : Form
  imp : Form -> Form -> Form

------------------------------------------------------------------------
-- The convertibility interpretation.  Atoms ¬¬(Conv) => every [[f]] ¬¬-stable.

intA : Eqn -> Set
intA (eqn a b) = Not (Not (PH.Conv a b))

intF : Form -> Set
intF (at e)    = intA e
intF bot       = Empty
intF (imp p q) = intF p -> intF q

negStable : {Z : Set} -> Not (Not (Not Z)) -> Not Z
negStable h z = h (\ nz -> nz z)

stab : (f : Form) -> Not (Not (intF f)) -> intF f
stab (at (eqn a b)) nn = negStable nn
stab bot            nn = nn (\ e -> e)
stab (imp p q)      nn = \ a -> stab q (\ k -> nn (\ f -> k (f a)))

------------------------------------------------------------------------
-- The (equational / recursor) axioms of T0 and their Conv-validity.

data Axiom : Form -> Set where
  axRO     : (y : Tm)     -> Axiom (at (eqn (ad ze y) y))
  axRS     : (x y : Tm)   -> Axiom (at (eqn (ad (su x) y) (su (ad x y))))
  axRefl   : (t : Tm)     -> Axiom (at (eqn t t))
  axSym    : (a b : Tm)   -> Axiom (imp (at (eqn a b)) (at (eqn b a)))
  axTrans  : (a b c : Tm) -> Axiom (imp (at (eqn a b)) (imp (at (eqn b c)) (at (eqn a c))))
  axCongS  : (a b : Tm)   -> Axiom (imp (at (eqn a b)) (at (eqn (su a) (su b))))
  axCongA1 : (a b c : Tm) -> Axiom (imp (at (eqn a b)) (at (eqn (ad a c) (ad b c))))
  axCongA2 : (a b c : Tm) -> Axiom (imp (at (eqn a b)) (at (eqn (ad c a) (ad c b))))
  axSinj   : (a b : Tm)   -> Axiom (imp (at (eqn (su a) (su b))) (at (eqn a b)))
  axSnz    : (t : Tm)     -> Axiom (imp (at (eqn (su t) ze)) bot)

ddRet : {Z : Set} -> Z -> Not (Not Z)
ddRet z k = k z

axiomValid : {f : Form} -> Axiom f -> intF f
axiomValid (axRO y)         = ddRet (PH.cstep (PS.stO y))
axiomValid (axRS x y)       = ddRet (PH.cstep (PS.stS x y))
axiomValid (axRefl t)       = ddRet PH.crefl
axiomValid (axSym a b)      = \ nnc k -> nnc (\ c -> k (PH.csym c))
axiomValid (axTrans a b c)  = \ nnab nnbc k -> nnab (\ cab -> nnbc (\ cbc -> k (PH.ctrans cab cbc)))
axiomValid (axCongS a b)    = \ nnc k -> nnc (\ c -> k (ES.convSu c))
axiomValid (axCongA1 a b c) = \ nnc k -> nnc (\ c -> k (ES.convAd1 c))
axiomValid (axCongA2 a b c) = \ nnc k -> nnc (\ c -> k (ES.convAd2 c))
axiomValid (axSinj a b)     = \ nnc k -> nnc (\ c -> k (CI.convSuInj c))
axiomValid (axSnz t)        = \ nnc -> nnc (\ c -> pe (CI.zeNotConvSuT t (PH.csym c)))

------------------------------------------------------------------------
-- T0 as a HILBERT system: equational axioms + classical propositional
-- schemas (K, S, double-negation, ex-falso) + modus ponens.  No cut, no
-- sequents -- exactly Guard's "closed axiom instances + MP".

data ThmT0 : Form -> Set where
  hAx  : {f : Form}   -> Axiom f -> ThmT0 f
  hK   : (p q : Form) -> ThmT0 (imp p (imp q p))
  hS   : (p q r : Form) ->
         ThmT0 (imp (imp p (imp q r)) (imp (imp p q) (imp p r)))
  hDN  : (p : Form)   -> ThmT0 (imp (imp (imp p bot) bot) p)
  hEFQ : (p : Form)   -> ThmT0 (imp bot p)
  hMP  : {p q : Form} -> ThmT0 (imp p q) -> ThmT0 p -> ThmT0 q

------------------------------------------------------------------------
-- SOUNDNESS: one structural induction.  MP is just a sound rule; the classical
-- schema hDN is validated by ¬¬-stability (stab).

sound : {f : Form} -> ThmT0 f -> intF f
sound (hAx a)     = axiomValid a
sound (hK p q)    = \ a _ -> a
sound (hS p q r)  = \ f g a -> f a (g a)
sound (hDN p)     = stab p
sound (hEFQ p)    = \ e -> emptyElim e
sound (hMP t1 t2) = (sound t1) (sound t2)

------------------------------------------------------------------------
-- Con(T0):  0 = s0  is not a theorem of T0.

zncG : Not (PH.Conv ze (su ze))
zncG c = pe (PH.zeNotConvSuZe c)

conT0 : Not (ThmT0 (at (eqn ze (su ze))))
conT0 t = sound t zncG
