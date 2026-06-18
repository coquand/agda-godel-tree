module T4.deduction where

{-

 A. Turing     1944 The Reform of Mathematical Notation and Phraseology

 "The deduction theorem should therefore be as well known as integration by parts"

-}

{-

 The deduction theorem tells us that in order to prove A => B from a list of hypotheses G
 it is enough to add A to the list G and then prove B from this extended list

 We need first to define what it means to prove a sentence from a list of hypotheses

    -either the sentence is in the list
    -or the sentence is an instance of an axiom (here two axioms S and K)
    -or the sentence can be deduced from modus-ponens: we have deduced A => B and we have deduced A
    and we deduce B by modus-ponens

 This definition is inductive:
       we define G |- A read "A is deduced from the hypotheses G" by induction

 We show then -by induction- that if G, A |- B then we have G |- A => B

 We have a lot of cases

 One key case is that we have G, A |- C => B and G, A |- C
 By -induction- we have G |- A => (C => B) and G |- A => C
 We want G |- A => B
 This is exactly where the axiom S plays a role

-}

data Nat : Set where
 zero : Nat
 suc  : Nat -> Nat

data list (A : Set) : Set where
 nil : list A
 cons : A -> list A -> list A

-- Form is the data type of "formulae", built only from atoms and implication
data Form : Set  where
 imply : Form -> Form -> Form
 atom  : Nat -> Form

-- context is the type of list of formulae
-- the terminology "context" comes from the system AUTOMATH
context : Set
context = list Form

-- nicer notation for implication
infixr 10 _=>_
_=>_ : Form -> Form -> Form
X => Y = imply X Y

-- nicer notation for contexts
infixr 10 _,_
_,_ : context -> Form -> context
G , X = cons X G

-- a formulae is in a context
data isIn : context -> Form -> Set where
 zero : {X : Form} -> {G : context} ->
             isIn (G , X) X
 suc : {X Y : Form} -> {G : context} ->
             isIn G X ->
             isIn (G , Y) X 

infixr 6 _⊢_

-- defines when a formula is a consequence of a list of hypotheses
data _⊢_ : context -> Form -> Set where
 var : {X : Form} -> {G : context} -> isIn G X -> G ⊢ X
 axK : {X Y : Form} -> {G : context} -> G ⊢ X => (Y => X)
 axS : {X Y Z : Form} -> {G : context} -> G ⊢ (X => (Y => Z)) => ((X => Y) => (X => Z))
 mp : {Y X : Form} -> {G : context} ->
      G ⊢ Y => X ->
      G ⊢ Y ->
      -------------
      G ⊢ X

-- 3 general lemmas used for proving the deduction theorem

dedlem1 : {G : context} -> {X : Form} -> G ⊢ X => X
dedlem1 {G} {X} = mp (mp axS axK) (axK {Y = X => X})

dedlem2 : {G : context} -> {X Y : Form} -> G ⊢ Y -> G ⊢ X => Y
dedlem2 d = mp axK d

dedlem3 : {G : context} -> {X Y : Form} -> isIn (G , X) Y -> G ⊢ X => Y
dedlem3 zero = dedlem1
dedlem3 (suc h) = mp axK (var h)

dedthm : {G : context} -> {X Y : Form} ->
         G , X ⊢ Y ->
         --------------
         G ⊢ X => Y

dedthm (var x) = dedlem3 x
dedthm axK = dedlem2 axK
dedthm axS = dedlem2 axS
dedthm (mp h h1) = mp (mp axS (dedthm h)) (dedthm h1)

dedcor1 : {G : context} -> {X : Form} -> G ⊢ X => X
dedcor1 {G} {X} = dedthm (var zero)

dedcor2 : {G : context} -> {X Y Z : Form} -> G ⊢ (X => (Y => Z)) => (Y => (X => Z))
dedcor2 {G} {X} {Y} {Z} =
 dedthm (dedthm (dedthm (mp (mp (var (suc (suc zero))) (var zero)) (var (suc zero)))))

dedcor3 : {G : context} -> {X Y Z : Form} -> G ⊢ (X => (Y => Z)) => ((X => Y) => X => Z)
dedcor3 {G} {X} {Y} {Z} =
 dedthm (dedthm (dedthm (mp (mp (var (suc (suc zero))) (var zero))
                        (mp (var (suc zero)) (var zero)))))

-- Composition / transitivity of implication, as an object-level theorem.
-- In context  G , (A => B) , (B => C) , A  we prove C by applying
-- (A => B) to A to get B, then (B => C) to B; discharging the three
-- hypotheses with dedthm yields the implication chain.
dedcor4 : {G : context} -> {A B C : Form} -> G ⊢ (A => B) => ((B => C) => (A => C))
dedcor4 {G} {A} {B} {C} =
 dedthm (dedthm (dedthm (mp (var (suc zero)) (mp (var (suc (suc zero))) (var zero)))))

-- The K-like combinator  A => (B => (C => A)).
-- In context  G , A , B , C  the goal A is simply the hypothesis A,
-- sitting two slots back; the three dedthm wrap it in the implications.
dedcor5 : {G : context} -> {A B C : Form} -> G ⊢ A => (B => (C => A))
dedcor5 {G} {A} {B} {C} =
 dedthm (dedthm (dedthm (var (suc (suc zero)))))




-- What is the normal form of decor?


-- ============================================================
-- The Carneiro derivation of the flip combinator.
--
-- This obtains the SAME result as dedcor2, but WITHOUT the
-- deduction theorem: it is point-free, using only mp / axS / axK
-- through a few combinators (the "Carneiro lift").
-- ============================================================

-- K-lift: carry an extra hypothesis R in front of a derived Q.
liftP : {G : context} -> {Q : Form} -> (R : Form) -> G ⊢ Q -> G ⊢ R => Q
liftP R D = mp axK D

-- One-level S: apply under a hypothesis X.
bComb : {G : context} -> {X Y Z : Form} ->
        G ⊢ X => (Y => Z) -> G ⊢ X => Y -> G ⊢ X => Z
bComb D1 D2 = mp (mp axS D1) D2

-- Two-level S: apply under two hypotheses X1 , X2.
bCombTwo : {G : context} -> {X1 X2 Y Z : Form} ->
           G ⊢ X1 => (X2 => (Y => Z)) ->
           G ⊢ X1 => (X2 => Y) ->
           G ⊢ X1 => (X2 => Z)
bCombTwo {X1 = X1} D1 D2 = bComb (bComb (liftP X1 axS) D1) D2

-- Transitivity of implication as a derivation.
impTransD : {G : context} -> {X Y Z : Form} ->
            G ⊢ X => Y -> G ⊢ Y => Z -> G ⊢ X => Z
impTransD pq qr = mp (mp axS (mp axK qr)) pq

-- The flip / C-combinator, derived a la Carneiro (cf. T4/mario.agda).
flipImp : {G : context} -> {X Y Z : Form} ->
          G ⊢ (X => (Y => Z)) => (Y => (X => Z))
flipImp {G} {X} {Y} {Z} =
  let Y' : Form
      Y' = (X => Y) => (X => Z)

      dYZ : G ⊢ Y' => (Y => (X => Z))
      dYZ = bCombTwo {X1 = Y'} {X2 = Y} {Y = X => Y} {Z = X => Z}
              (axK {X = Y'} {Y = Y})
              (liftP Y' (axK {X = Y} {Y = X}))
  in impTransD axS dYZ

-- ============================================================
-- Normal-form comparison of the two flip derivations.
--
-- Both dedcor2 (via the deduction theorem) and flipImp (direct,
-- Carneiro lift) are closed terms of the SAME inductive type _⊢_,
-- so each has a genuine normal form: a finite tree of
-- var / axK / axS / mp.  Computed at X,Y,Z := atom 0,1,2 and G := nil
-- (the structure is independent of these choices):
--
--   * Both reduce to pure axS / axK / mp trees, with NO var -- the
--     hypotheses are fully discharged in each case.
--   * They are NOT the same normal form (not definitionally equal).
--
--   derivation   route                       nodes
--   ----------   -------------------------   -----
--   flipImp      direct (Carneiro lift)         19
--   dedcor2      deduction theorem             161
--
-- The normal form of flipImp (compact: S/K placed by hand exactly
-- where needed) is
--
--   mp (mp axS
--          (mp axK (mp (mp axS (mp (mp axS (mp axK axS)) axK))
--                      (mp axK axK))))
--      axS
--
-- dedcor2 normalises to a 161-node tree of the same vocabulary.
--
-- Why the blow-up: dedthm is a structural recursion that rewrites
-- the WHOLE proof tree --
--   dedthm (mp h h1) = mp (mp axS (dedthm h)) (dedthm h1)
-- replaces every mp by an mp-of-mp-of-axS AND recurses into both
-- subtrees; every leaf axiom becomes mp axK _ (a K-lift); and
-- var zero unfolds to dedlem1 = mp (mp axS axK) axK (5 nodes).
-- dedcor2 nests dedthm THREE times, so this expansion compounds
-- multiplicatively -- hence 161 vs 19.
--
-- This answers "What is the normal form of decor?" above: the
-- deduction theorem is a convenient meta-level tactic, but
-- normalising its output yields a far larger object-level S/K term
-- than a direct derivation of the same theorem.
-- ============================================================


-- ============================================================
-- A second example: the W (contraction) combinator.
--
-- W "diagonalises" a hypothesis:  (X => (X => Y)) => (X => Y),
-- i.e. given a proof of X => X => Y, one copy of X suffices.
-- As with flip, we derive it two ways and compare normal forms.
-- ============================================================

-- Route 1: via the deduction theorem.
-- In context  G , (X => X => Y) , X  we prove Y by feeding the
-- single hypothesis X twice, then discharge X and (X => X => Y).
dedW : {G : context} -> {X Y : Form} -> G ⊢ (X => (X => Y)) => (X => Y)
dedW = dedthm (dedthm (mp (mp (var (suc zero)) (var zero)) (var zero)))

-- Route 2: direct, point-free (Carneiro lift).
-- axS at (X,X,Y) gives  (X=>X=>Y) => (X=>X) => (X=>Y);
-- bComb applies it under the hypothesis (X=>X=>Y) to the lifted
-- identity dedlem1 : X => X, contracting (X=>X) away.
wImp : {G : context} -> {X Y : Form} -> G ⊢ (X => (X => Y)) => (X => Y)
wImp {G} {X} {Y} =
  bComb (axS {X = X} {Y = X} {Z = Y}) (liftP (X => (X => Y)) dedlem1)

-- ============================================================
-- Normal-form comparison (computed at X,Y := atom 0,1, G := nil;
-- the structure is independent of these choices).  As with flip,
-- both are closed terms of _⊢_ and reduce to pure axS/axK/mp
-- trees with NO var, but they are not the same normal form.
--
--   derivation   route                       nodes
--   ----------   -------------------------   -----
--   wImp         direct (Carneiro lift)         11
--   dedW         deduction theorem              59
--
-- Normal form of wImp (compact: one S to split the application,
-- one K-lift of the identity dedlem1):
--
--   mp (mp axS axS) (mp axK (mp (mp axS axK) axK))
--
-- Normal form of dedW (59 nodes):
--
--   mp (mp axS
--          (mp (mp axS (mp axK axS))
--              (mp (mp axS
--                      (mp (mp axS (mp axK axS))
--                          (mp (mp axS (mp axK axK)) (mp (mp axS axK) axK))))
--                  (mp (mp axS (mp (mp axS (mp axK axS)) (mp axK axK)))
--                      (mp axK axK)))))
--      (mp (mp axS (mp (mp axS (mp axK axS)) (mp axK axK))) (mp axK axK))
--
-- Same moral as flip, and same cause: dedW nests dedthm twice, and
-- each nesting rewrites the whole proof tree (every mp becomes an
-- mp-of-mp-of-axS and recurses into both subtrees; every leaf axiom
-- becomes a K-lift; var zero unfolds to dedlem1 = mp (mp axS axK) axK,
-- 5 nodes).  Hence 59 via the theorem vs 11 placing S/K by hand.
-- (Flip needed three dedthm nestings -> 161 vs 19; W needs two,
-- a milder but identical blow-up.)
-- ============================================================


-- ============================================================
-- A third example: composition / transitivity of implication.
--   (A => B) => ((B => C) => (A => C))
-- The deduction-theorem route is dedcor4 above; here is the
-- direct, point-free derivation (Carneiro lift).
-- ============================================================

-- The natural B-combinator  (B => C) => ((A => B) => (A => C)) is
-- axS specialised at X := A, fed a K-lifted hypothesis: axK gives
--   (B=>C) => (A => (B=>C))
-- which impTransD chains into
--   axS : (A => (B=>C)) => ((A=>B) => (A=>C)).
-- compImp then just flips the first two arguments with flipImp.
compImp : {G : context} -> {A B C : Form} -> G ⊢ (A => B) => ((B => C) => (A => C))
compImp {G} {A} {B} {C} =
  mp (flipImp {X = B => C} {Y = A => B} {Z = A => C})
     (impTransD (axK {X = B => C} {Y = A}) (axS {X = A} {Y = B} {Z = C}))

-- Normal-form comparison (computed at A,B,C := atom 0,1,2, G := nil;
-- the structure is independent of these choices).  Both are closed
-- terms of _⊢_ reducing to pure axS/axK/mp trees with NO var.
--
--   derivation   route                       nodes
--   ----------   -------------------------   -----
--   compImp      direct (Carneiro lift)         27
--   dedcor4      deduction theorem             161
--
-- Normal form of compImp: the 19-node flip core (flipImp) applied to
-- a 7-node composition (impTransD axK axS), i.e. mp <flip> <comp>:
--
--   mp (mp (mp axS (mp axK (mp (mp axS (mp (mp axS (mp axK axS)) axK))
--                              (mp axK axK)))) axS)
--      (mp (mp axS (mp axK axS)) axK)
--
-- dedcor4 nests dedthm THREE times (like flip), so its output
-- normalises to a 161-node tree -- the very same size as dedcor2.
-- The per-mp expansion of the deduction theorem (every mp becomes
-- mp-of-mp-of-axS and recurses into both subtrees; every leaf axiom
-- becomes a K-lift) compounds multiplicatively over the three
-- nestings, hence 161 vs 27.
-- ============================================================


-- ============================================================
-- A fourth example: the nested-K (constant) combinator.
--   A => (B => (C => A))
-- The deduction-theorem route is dedcor5 above; here is the
-- direct, point-free derivation (Carneiro lift).
-- ============================================================

-- Two K's chained:  axK : A => (C => A)  is composed (impTransD)
-- with  axK : (C => A) => (B => (C => A)).
constImp : {G : context} -> {A B C : Form} -> G ⊢ A => (B => (C => A))
constImp {G} {A} {B} {C} =
  impTransD (axK {X = A} {Y = C}) (axK {X = C => A} {Y = B})

-- Normal-form comparison (A,B,C := atom 0,1,2, G := nil).
--
--   derivation   route                       nodes
--   ----------   -------------------------   -----
--   constImp     direct (Carneiro lift)          7
--   dedcor5      deduction theorem              29
--
-- Normal form of constImp (impTransD of two axK):
--
--   mp (mp axS (mp axK axK)) axK
--
-- Normal form of dedcor5 (29 nodes):
--
--   mp (mp axS (mp (mp axS (mp axK axS))
--                  (mp (mp axS (mp axK axK)) (mp axK axK))))
--      (mp (mp axS (mp axK axK)) (mp (mp axS axK) axK))
--
-- Same moral once more.  Here the meta-proof is maximally trivial --
-- "A is the hypothesis sitting two slots back" -- yet three dedthm
-- nestings still rewrite it into a 29-node S/K term, versus 7 nodes
-- placing the two K's by hand.  The deduction theorem trades brevity
-- of the meta-proof for size of the object-proof.
-- ============================================================


-- ============================================================
-- A fifth example: the "apply" combinator (modus ponens as a
-- formula).
--   A => ((A => B) => B)
-- Given A and a proof of A => B, modus ponens yields B; this
-- internalises that as an object-level theorem.
-- ============================================================

-- Deduction-theorem route.  In context  G , A , (A => B)  we prove
-- B by applying (A => B) to A, then discharge both hypotheses.
dedcor6 : {G : context} -> {A B : Form} -> G ⊢ A => ((A => B) => B)
dedcor6 {G} {A} {B} = dedthm (dedthm (mp (var zero) (var (suc zero))))

-- Direct route (Carneiro lift).  apply is just flip of the identity:
-- dedlem1 : (A=>B) => (A=>B)  is  (A=>B) => (A => B), and flipImp
-- swaps its first two arguments into  A => ((A=>B) => B).
applyImp : {G : context} -> {A B : Form} -> G ⊢ A => ((A => B) => B)
applyImp {G} {A} {B} = mp (flipImp {X = A => B} {Y = A} {Z = B}) (dedlem1 {X = A => B})

-- Normal-form comparison (A,B := atom 0,1, G := nil).  Both reduce
-- to pure axS/axK/mp trees with NO var.
--
--   derivation   route                       nodes
--   ----------   -------------------------   -----
--   applyImp     direct (Carneiro lift)         25
--   dedcor6      deduction theorem              35
--
-- Normal form of applyImp: the 19-node flip core (flipImp) applied
-- to the 5-node identity dedlem1 = mp (mp axS axK) axK:
--
--   mp (mp (mp axS (mp axK (mp (mp axS (mp (mp axS (mp axK axS)) axK))
--                              (mp axK axK)))) axS)
--      (mp (mp axS axK) axK)
--
-- Normal form of dedcor6 (35 nodes):
--
--   mp (mp axS (mp (mp axS (mp axK axS))
--                  (mp (mp axS (mp (mp axS (mp axK axS)) (mp axK axK)))
--                      (mp axK axK))))
--      (mp (mp axS (mp axK axK)) (mp (mp axS axK) axK))
--
-- This example nests dedthm only TWICE (like W), so the blow-up is
-- mild: 35 vs 25.  The deduction-theorem proof is the most natural
-- one to write -- "apply the hypothesis A => B to A" -- but the
-- direct derivation, reading apply as flip of the identity, is still
-- the smaller object-level term.
-- ============================================================
