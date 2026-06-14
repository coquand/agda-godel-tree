{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.G3ConT0 -- the CAPSTONE of the LOGICAL terminal (attempt3 §8/§9/§13,
-- stages G4-G5-G6): the META proof that the FULL induction-free theory T0
-- (closed equational/recursor axioms + classical propositional logic + MP) is
-- CONSISTENT, i.e.  T0 |/- (0 = s0).
--
-- It plugs the G3p logical layer (T4.G3Logic: cut-free derivability with cut
-- ADMISSIBLE) into the Church-Rosser terminal's convertibility interface
-- (T4.ConvInterface: L1 congruence, L2 s-injectivity, L3 clash), exactly the
-- §13.4 contract.  The bridge is SEMANTIC SOUNDNESS of G3p over the Conv-model:
--
--   * atoms (a = b)  are interpreted as  ¬¬ (Conv a b)  -- the double negation
--     makes every formula's interpretation ¬¬-STABLE, which is what makes
--     CLASSICAL (multi-succedent) sequent soundness constructively provable
--     in Agda (the R-> case needs stability of the succedent formula);
--   * each T0 axiom is VALID in this model  (axiomValid, via L1/L2/L3 + crefl/
--     csym/ctrans + the recursor steps);
--   * 0 = s0 is NOT valid  (zeNotConvSuZe, L3);
--   * hence (soundness) 0 = s0 is not derivable from the axioms  -> conT0.
--
-- MP is admissible (mp, via T4.G3Logic.cutP = cut elimination), so this G3p
-- derivability really is T0 (closed axioms + MP), not a weaker fragment.
--
-- All meta, over the toy recursor TRS (ze/su/ad); the real-system version reuses
-- the identical structure.  ASCII, --safe --without-K --exact-split, no holes.

module T4.G3ConT0 where

import T4.ParReflPres as PR
import T4.ParStep     as PS
import T4.ParHeadline as PH
import T4.EqSound     as ES
import T4.ConvInterface as CI

open PR using ( Tm ; ze ; su ; ad )

------------------------------------------------------------------------
-- Atoms of T0 = equations between toy terms; instantiate the G3p logic at them.

data Eqn : Set where
  eqn : Tm -> Tm -> Eqn

open import T4.G3Logic Eqn

------------------------------------------------------------------------
-- A unit type and the bridge from the CR terminal's Empty to ours.

data Unit : Set where unit : Unit

pe : PH.Empty -> Empty
pe ()

------------------------------------------------------------------------
-- Interpretation.  Atoms ¬¬(Conv) -> every interpretation is ¬¬-stable.

intA : Eqn -> Set
intA (eqn a b) = Not (Not (PH.Conv a b))

intF : Form -> Set
intF (at e)    = intA e
intF bot       = Empty
intF (imp p q) = intF p -> intF q

intAnt : List -> Set
intAnt []        = Unit
intAnt (f :: G)  = And (intF f) (intAnt G)

intNeg : List -> Set
intNeg []        = Unit
intNeg (f :: D)  = And (Not (intF f)) (intNeg D)

------------------------------------------------------------------------
-- Double-negation stability of every interpreted formula.

negStable : {Z : Set} -> Not (Not (Not Z)) -> Not Z
negStable h z = h (\ nz -> nz z)

stab : (f : Form) -> Not (Not (intF f)) -> intF f
stab (at (eqn a b)) nn = negStable nn
stab bot            nn = nn (\ e -> e)
stab (imp p q)      nn = \ a -> stab q (\ k -> nn (\ f -> k (f a)))

------------------------------------------------------------------------
-- Lookups / context decomposition for the interpretation.

lookupAnt : {f : Form} {G : List} -> Mem f G -> intAnt G -> intF f
lookupAnt memHd     (mkAnd x _)   = x
lookupAnt (memTl m) (mkAnd _ env) = lookupAnt m env

lookupNeg : {f : Form} {D : List} -> Mem f D -> intNeg D -> Not (intF f)
lookupNeg memHd     (mkAnd n _)   = n
lookupNeg (memTl m) (mkAnd _ neg) = lookupNeg m neg

delAnt : {f : Form} {G G0 : List} -> Del f G G0 -> intAnt G -> And (intF f) (intAnt G0)
delAnt delHd     env           = env
delAnt (delTl d) (mkAnd x env) = let r = delAnt d env in mkAnd (andL r) (mkAnd x (andR r))

delNeg : {f : Form} {D D0 : List} -> Del f D D0 -> intNeg D -> And (Not (intF f)) (intNeg D0)
delNeg delHd     neg           = neg
delNeg (delTl d) (mkAnd n neg) = let r = delNeg d neg in mkAnd (andL r) (mkAnd n (andR r))

------------------------------------------------------------------------
-- SEMANTIC SOUNDNESS of G3p in the refutation interpretation:
--   a derivation of  G |- D  refutes (intAnt G  with  intNeg D).

sound : {n : Nat} {G D : List} -> Der n G D -> intAnt G -> intNeg D -> Empty
sound (init p i j)     env neg = lookupNeg j neg (lookupAnt i env)
sound (lbot i)         env neg = lookupAnt i env
sound (limp del d1 d2) env neg =
  let r    = delAnt del env
      f    = andL r
      env0 = andR r
  in sound d1 env0 (mkAnd (\ a -> sound d2 (mkAnd (f a) env0) neg) neg)
sound (rimp {B = B} del d) env neg =
  let r    = delNeg del neg
      nf   = andL r
      neg0 = andR r
  in nf (\ a -> stab B (\ k -> sound d (mkAnd a env) (mkAnd k neg0)))

------------------------------------------------------------------------
-- The axioms of T0 (closed instances of the schemas) and their Conv-validity.

data Axiom : Form -> Set where
  axRO    : (y : Tm)     -> Axiom (at (eqn (ad ze y) y))
  axRS    : (x y : Tm)   -> Axiom (at (eqn (ad (su x) y) (su (ad x y))))
  axRefl  : (t : Tm)     -> Axiom (at (eqn t t))
  axSym   : (a b : Tm)   -> Axiom (imp (at (eqn a b)) (at (eqn b a)))
  axTrans : (a b c : Tm) -> Axiom (imp (at (eqn a b)) (imp (at (eqn b c)) (at (eqn a c))))
  axCongS : (a b : Tm)   -> Axiom (imp (at (eqn a b)) (at (eqn (su a) (su b))))
  axCongA1 : (a b c : Tm) -> Axiom (imp (at (eqn a b)) (at (eqn (ad a c) (ad b c))))
  axCongA2 : (a b c : Tm) -> Axiom (imp (at (eqn a b)) (at (eqn (ad c a) (ad c b))))
  axSinj  : (a b : Tm)   -> Axiom (imp (at (eqn (su a) (su b))) (at (eqn a b)))
  axSnz   : (t : Tm)     -> Axiom (imp (at (eqn (su t) ze)) bot)

ddRet : {Z : Set} -> Z -> Not (Not Z)
ddRet z k = k z

axiomValid : {f : Form} -> Axiom f -> intF f
axiomValid (axRO y)        = ddRet (PH.cstep (PS.stO y))
axiomValid (axRS x y)      = ddRet (PH.cstep (PS.stS x y))
axiomValid (axRefl t)      = ddRet PH.crefl
axiomValid (axSym a b)     = \ nnc k -> nnc (\ c -> k (PH.csym c))
axiomValid (axTrans a b c) = \ nnab nnbc k -> nnab (\ cab -> nnbc (\ cbc -> k (PH.ctrans cab cbc)))
axiomValid (axCongS a b)   = \ nnc k -> nnc (\ c -> k (ES.convSu c))
axiomValid (axCongA1 a b c) = \ nnc k -> nnc (\ c -> k (ES.convAd1 c))
axiomValid (axCongA2 a b c) = \ nnc k -> nnc (\ c -> k (ES.convAd2 c))
axiomValid (axSinj a b)    = \ nnc k -> nnc (\ c -> k (CI.convSuInj c))
axiomValid (axSnz t)       = \ nnc -> nnc (\ c -> pe (CI.zeNotConvSuT t (PH.csym c)))

------------------------------------------------------------------------
-- An axiom CONTEXT is a list of closed axiom instances; all are valid.

AllAx : List -> Set
AllAx []        = Unit
AllAx (f :: G)  = And (Axiom f) (AllAx G)

allAxValid : {G : List} -> AllAx G -> intAnt G
allAxValid {[]}     unit          = unit
allAxValid {f :: G} (mkAnd ax xs) = mkAnd (axiomValid ax) (allAxValid xs)

------------------------------------------------------------------------
-- T0-provability of phi: derivable (cut-free; cut is admissible) from some
-- finite context of closed axiom instances.

T0Provable : Form -> Set
T0Provable f = Sigma List (\ Ax -> And (AllAx Ax) (Prov Ax (f :: [])))

-- MP is admissible (so T0Provable really is "axioms + MP"): via cut elimination.

provWkS : {G D : List} (A : Form) -> Prov G D -> Prov G (A :: D)
provWkS A (mkSig m p) = mkSig m (wkS A p)

provInvR : {A B : Form} {G D0 : List} -> Prov G (imp A B :: D0) -> Prov (A :: G) (B :: D0)
provInvR (mkSig m p) = mkSig m (invR' m p)

mp : {Ax : List} {A B : Form} ->
     Prov Ax (A :: []) -> Prov Ax (imp A B :: []) -> Prov Ax (B :: [])
mp {Ax} {A} {B} p1 p2 =
  cutP A (provPermS permSwap (provWkS B p1)) (provInvR p2)

------------------------------------------------------------------------
-- Con(T0):  0 = s0  is NOT a theorem of T0.

tripleNeg : {X : Set} -> Not X -> Not (Not (Not X))
tripleNeg nx nnx = nnx nx

zncG : Not (PH.Conv ze (su ze))
zncG c = pe (PH.zeNotConvSuZe c)

conT0 : Not (T0Provable (at (eqn ze (su ze))))
conT0 (mkSig Ax (mkAnd allAx (mkSig n d))) =
  sound d (allAxValid allAx) (mkAnd (tripleNeg zncG) unit)
