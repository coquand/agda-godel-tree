{-# OPTIONS --without-K --exact-split #-}

module ChwistekCodeQuant where

open import ChwistekSyntax
open import ChwistekDiagonal
open import ChwistekProvability
open import ChwistekCodeLogic

------------------------------------------------------------------------
-- A. Code-variable lifting and substitution in CExp
------------------------------------------------------------------------

-- liftCExp : shift all free code variables up by one
liftCExp : CExp -> CExp
liftCExp (cvar v)   = cvar (cvs v)
liftCExp (clit c)   = clit c
liftCExp (ccheck e)   = ccheck (liftCExp e)
liftCExp (csub e1 e2) = csub (liftCExp e1) (liftCExp e2)

-- substCExp0 : substitute s for code variable 0 in e
substCExp0 : CExp -> CExp -> CExp
substCExp0 s (cvar cvz)     = s
substCExp0 s (cvar (cvs v)) = cvar v
substCExp0 s (clit c)       = clit c
substCExp0 s (ccheck e)     = ccheck (substCExp0 s e)
substCExp0 s (csub e1 e2)   = csub (substCExp0 s e1) (substCExp0 s e2)

------------------------------------------------------------------------
-- B. Code-variable substitution in Formula
------------------------------------------------------------------------

-- substFormulaCode0 : substitute s for code variable 0 in a formula
-- This is independent of term substitution.
-- fcAll binds a code variable, so we lift under it.
-- fall binds a term variable, so no lifting of code vars.

substFormulaCode0 : CExp -> Formula -> Formula
substFormulaCode0 s fbot         = fbot
substFormulaCode0 s (feq t u)    = feq t u     -- no code vars in terms
substFormulaCode0 s (fimp a b)   = fimp (substFormulaCode0 s a)
                                        (substFormulaCode0 s b)
substFormulaCode0 s (fall a)     = fall (substFormulaCode0 s a)
substFormulaCode0 s (fcode c)    = fcode c      -- no code vars in Code
substFormulaCode0 s (fceq e1 e2) = fceq (substCExp0 s e1)
                                        (substCExp0 s e2)
substFormulaCode0 s (fcAll a)    = fcAll (substFormulaCode0 (liftCExp s) a)

------------------------------------------------------------------------
-- C. Evaluation of closed code expressions
------------------------------------------------------------------------

-- evalCExp evaluates a closed CExp to a Code value.
-- Open expressions (containing cvar) return nothing.
-- ccheck e evaluates e, runs checkProof, and returns encFormula of
-- the proved formula (if any).

evalCExp : CExp -> Maybe Code
evalCExp (cvar _)   = nothing
evalCExp (clit c)   = just c
evalCExp (ccheck e) =
  maybeBind (evalCExp e) (\ p ->
  maybeBind (checkProof p) (\ a ->
  just (encFormula a)))
evalCExp (csub e1 e2) =
  maybeBind (evalCExp e1) (\ c1 ->
  maybeBind (evalCExp e2) (\ c2 ->
  maybeBind (decFormula c1) (\ a ->
  just (encFormula (substFormulaCode0 (clit c2) a)))))

------------------------------------------------------------------------
-- D. Computation lemmas
------------------------------------------------------------------------

substCExp0-var0 : (s : CExp) -> Eq (substCExp0 s (cvar cvz)) s
substCExp0-var0 s = refl

substCExp0-lit : (s : CExp) (c : Code) -> Eq (substCExp0 s (clit c)) (clit c)
substCExp0-lit s c = refl

substFormulaCode0-bot : (s : CExp) -> Eq (substFormulaCode0 s fbot) fbot
substFormulaCode0-bot s = refl

substFormulaCode0-fceq :
  (s e1 e2 : CExp) ->
  Eq (substFormulaCode0 s (fceq e1 e2))
     (fceq (substCExp0 s e1) (substCExp0 s e2))
substFormulaCode0-fceq s e1 e2 = refl

substFormulaCode0-fcAll :
  (s : CExp) (a : Formula) ->
  Eq (substFormulaCode0 s (fcAll a))
     (fcAll (substFormulaCode0 (liftCExp s) a))
substFormulaCode0-fcAll s a = refl

evalCExp-lit : (c : Code) -> Eq (evalCExp (clit c)) (just c)
evalCExp-lit c = refl

------------------------------------------------------------------------
-- E. Comments
------------------------------------------------------------------------

-- Why fcAll is needed:
--
--   The Goedel sentence must say "for all proof codes p,
--   checkProof(p) is not my code." This requires quantifying
--   over code values inside formulas. fcAll provides this.
--   It is separate from fall (term quantification) to keep
--   the binding discipline clean.
--
-- Why this closes the expressive gap:
--
--   With fceq + fcAll + CExp, formulas can now express:
--
--     fcAll (fimp (fceq (ccheck (cvar cvz)) (clit c)) fbot)
--
--   which means "for all p, checkProof(p) != c" — i.e.,
--   "no proof code proves the formula with code c."
--
--   Combined with diagEnc (from ChwistekCodeLogic), which
--   computes encFormula(diag S) from encSchema S, we can
--   build a schema whose diagonal genuinely refers to its
--   own formula code.
--
-- Next step:
--
--   Define the Goedel schema:
--
--     Sg = schema whose instantiation with code c gives
--          fcAll (fimp (fceq (ccheck (cvar cvz)) (clit c)) fbot)
--
--   Then Gg = diag Sg says "I am not provable" via diagEnc.
