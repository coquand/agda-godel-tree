{-# OPTIONS --without-K --exact-split #-}

module ChwistekCodeLogic where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability

------------------------------------------------------------------------
-- Eq helper
------------------------------------------------------------------------

eqTrans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
eqTrans refl q = q

------------------------------------------------------------------------
-- A. Schema tag constants (matching encSchema in ChwistekDiagonal)
------------------------------------------------------------------------

-- encSchema uses tags:
--   catom n10 = shole
--   catom n11 = sconst
--   catom n12 = simp
--   catom n13 = sall

n10 : Nat
n10 = suc (suc (suc (suc (suc
       (suc (suc (suc (suc (suc
       zero)))))))))

n11 : Nat
n11 = suc n10

n12 : Nat
n12 = suc n11

n13 : Nat
n13 = suc n12

------------------------------------------------------------------------
-- B. Decode schemas from Code
------------------------------------------------------------------------

decSchema : Code -> Maybe Schema

decSchema (catom n) = h (eqNat n n10)
  where
  h : Bool -> Maybe Schema
  h true  = just shole
  h false = nothing

decSchema (cnode (catom n) rest) = h1 (eqNat n n11) n rest
  where
  h1 : Bool -> Nat -> Code -> Maybe Schema
  h1 true _ r = maybeMap sconst (decFormula r)
  h1 false m r = h2 (eqNat m n12) m r
    where
    h2 : Bool -> Nat -> Code -> Maybe Schema
    h2 true _ (cnode l r2) =
      maybeBind (decSchema l) (\ sl ->
      maybeBind (decSchema r2) (\ sr ->
      just (simp sl sr)))
    h2 true _ (catom _) = nothing
    h2 false m2 r2 = h3 (eqNat m2 n13) r2
      where
      h3 : Bool -> Code -> Maybe Schema
      h3 true r3 = maybeMap sall (decSchema r3)
      h3 false (catom _)   = nothing
      h3 false (cnode _ _)  = nothing

decSchema (cnode (cnode _ _) _) = nothing

------------------------------------------------------------------------
-- C. Roundtrip: decCVar (encCVar v) = just v
------------------------------------------------------------------------

decCVar-encCVar : (v : CVar) -> Eq (decCVar (encCVar v)) (just v)
decCVar-encCVar cvz     = refl
decCVar-encCVar (cvs v) =
  eqCong (maybeMap cvs) (decCVar-encCVar v)

------------------------------------------------------------------------
-- D. Roundtrip: decCExp (encCExp e) = just e
------------------------------------------------------------------------

decCExp-encCExp : (e : CExp) -> Eq (decCExp (encCExp e)) (just e)
decCExp-encCExp (cvar v)   =
  eqCong (maybeMap cvar) (decCVar-encCVar v)
decCExp-encCExp (clit c)   = refl
decCExp-encCExp (ccheck e) =
  eqCong (maybeMap ccheck) (decCExp-encCExp e)
decCExp-encCExp (csub e1 e2) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ de1 -> maybeBind (decCExp (encCExp e2))
              (\ de2 -> just (csub de1 de2))))
            (decCExp-encCExp e1))
    (eqCong (\ r -> maybeBind r (\ de2 -> just (csub e1 de2)))
            (decCExp-encCExp e2))

------------------------------------------------------------------------
-- E. Roundtrip: decFormula (encFormula A) = just A
------------------------------------------------------------------------

decFormula-encFormula : (A : Formula) -> Eq (decFormula (encFormula A)) (just A)

decFormula-encFormula fbot = refl

decFormula-encFormula (feq s t) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ ds -> maybeBind (decTerm (encTerm t))
              (\ dt -> just (feq ds dt))))
            (decTerm-encTerm s))
    (eqCong (\ r -> maybeBind r (\ dt -> just (feq s dt)))
            (decTerm-encTerm t))

decFormula-encFormula (fimp a b) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ da -> maybeBind (decFormula (encFormula b))
              (\ db -> just (fimp da db))))
            (decFormula-encFormula a))
    (eqCong (\ r -> maybeBind r (\ db -> just (fimp a db)))
            (decFormula-encFormula b))

decFormula-encFormula (fall a) =
  eqCong (maybeMap fall) (decFormula-encFormula a)

decFormula-encFormula (fcode c) = refl

decFormula-encFormula (fceq e1 e2) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ de1 -> maybeBind (decCExp (encCExp e2))
              (\ de2 -> just (fceq de1 de2))))
            (decCExp-encCExp e1))
    (eqCong (\ r -> maybeBind r (\ de2 -> just (fceq e1 de2)))
            (decCExp-encCExp e2))

decFormula-encFormula (fcAll a) =
  eqCong (maybeMap fcAll) (decFormula-encFormula a)

------------------------------------------------------------------------
-- F. Roundtrip: decSchema (encSchema S) = just S
------------------------------------------------------------------------

decSchema-encSchema : (S : Schema) -> Eq (decSchema (encSchema S)) (just S)

decSchema-encSchema shole = refl

decSchema-encSchema (sconst A) =
  eqCong (maybeMap sconst) (decFormula-encFormula A)

decSchema-encSchema (simp S T) =
  eqTrans
    (eqCong (\ r -> maybeBind r
              (\ sl -> maybeBind (decSchema (encSchema T))
              (\ sr -> just (simp sl sr))))
            (decSchema-encSchema S))
    (eqCong (\ r -> maybeBind r (\ sr -> just (simp S sr)))
            (decSchema-encSchema T))

decSchema-encSchema (sall S) =
  eqCong (maybeMap sall) (decSchema-encSchema S)

------------------------------------------------------------------------
-- E. Diagonal bridge
------------------------------------------------------------------------

-- diagFormula c: given the Code of a schema, return its diagonal Formula
diagFormula : Code -> Maybe Formula
diagFormula c = maybeBind (decSchema c) (\ S -> just (diag S))

-- diagEnc c: given the Code of a schema, return the Code of its diagonal
diagEnc : Code -> Maybe Code
diagEnc c = maybeMap encFormula (diagFormula c)

-- Bridge lemma: diagFormula computes the diagonal correctly
diagFormula-correct :
  (S : Schema) ->
  Eq (diagFormula (encSchema S)) (just (diag S))
diagFormula-correct S =
  eqCong (\ r -> maybeBind r (\ S' -> just (diag S')))
         (decSchema-encSchema S)

-- Bridge lemma: diagEnc computes the code of the diagonal correctly
diagEnc-correct :
  (S : Schema) ->
  Eq (diagEnc (encSchema S)) (just (encFormula (diag S)))
diagEnc-correct S =
  eqCong (maybeMap encFormula) (diagFormula-correct S)

------------------------------------------------------------------------
-- F. Concrete bridge for G
------------------------------------------------------------------------

-- G = diag Snot, so diagEnc applied to the code of Snot gives
-- the code of G.

G-bridge : Eq (diagEnc (encSchema Snot)) (just (encFormula G))
G-bridge = diagEnc-correct Snot

------------------------------------------------------------------------
-- G. Comments
------------------------------------------------------------------------

-- This file provides the COMPUTATIONAL BRIDGE between schema codes
-- and formula codes:
--
--   diagEnc-correct S : diagEnc (encSchema S) = just (encFormula (diag S))
--
-- Given the code of a schema S, we can COMPUTE the code of the
-- formula (diag S). This bridges the gap identified in ChwistekGodel1:
--
--   - diag feeds encSchema S (the schema code) to S
--   - the Goedel argument needs encFormula G (the formula code)
--   - diagEnc computes encFormula G from encSchema S
--
-- Key roundtrip lemmas proved:
--
--   decFormula-encFormula : decFormula (encFormula A) = just A
--   decSchema-encSchema  : decSchema (encSchema S)  = just S
--
-- These establish that encoding is injective (has a left inverse).
--
-- Next step: define a schema whose instantiation uses diagEnc
-- to refer to its own formula code, enabling a genuine Goedel
-- sentence that talks about its own provability.
