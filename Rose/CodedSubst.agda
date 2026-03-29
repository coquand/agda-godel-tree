{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.CodedSubst where

open import Rose.Base
  using (Nat; zero; suc; Maybe; nothing; just; maybeMap)
open import Rose.Tree using (Tree; lf; nd)
open import Rose.Code using (tagLeaf; tagVar; tagPair; tagCase; tagRec)

------------------------------------------------------------------------
-- Thick map on nat-codes (tree-encoded natural numbers).
--
-- thickNatCode k t: if t encodes nat k, return nothing;
-- otherwise return the adjusted nat-code.
-- This mirrors Rose.SubstAt.thick but on raw trees.

thickNatCode : Nat -> Tree -> Maybe Tree
thickNatCode zero    lf       = nothing
thickNatCode zero    (nd a t) = just t
thickNatCode (suc k) lf       = just lf
thickNatCode (suc k) (nd a t) = maybeMap (nd a) (thickNatCode k t)

------------------------------------------------------------------------
-- Apply the thick result to get a substitution outcome.

thickVarResult : Tree -> Maybe Tree -> Tree
thickVarResult repl nothing  = repl
thickVarResult repl (just t) = nd tagVar t

------------------------------------------------------------------------
-- Variable substitution: combine thick and result.

codedSubstVar : Tree -> Nat -> Tree -> Tree
codedSubstVar repl i varcode = thickVarResult repl (thickNatCode i varcode)

------------------------------------------------------------------------
-- Coded substitution for closed replacement.
--
-- codedSubst repl i code
--
--   repl  = tree-code of the replacement term (must be closed)
--   i     = target variable index (as a Nat)
--   code  = tree-code of the term being traversed
--
-- This is the binary-tree analogue of Rose's st(x, y, z).

mutual

  codedSubst : Tree -> Nat -> Tree -> Tree
  codedSubst repl i lf = lf
  codedSubst repl i (nd tag payload) =
    codedSubstTagged repl i tag payload

  codedSubstTagged : Tree -> Nat -> Tree -> Tree -> Tree
  -- tag 0 = lf = tagLeaf: no variables
  codedSubstTagged repl i lf payload =
    nd lf payload
  -- tag 1 = nd lf lf = tagVar: variable case
  codedSubstTagged repl i (nd lf lf) payload =
    codedSubstVar repl i payload
  -- tag 2 = tagPair: recurse on both children
  codedSubstTagged repl i (nd lf (nd lf lf)) lf =
    nd tagPair lf
  codedSubstTagged repl i (nd lf (nd lf lf)) (nd ct cu) =
    nd tagPair (nd (codedSubst repl i ct) (codedSubst repl i cu))
  -- tag 3 = tagCase: recurse, step index shifts by 2
  codedSubstTagged repl i (nd lf (nd lf (nd lf lf))) lf =
    nd tagCase lf
  codedSubstTagged repl i (nd lf (nd lf (nd lf lf))) (nd ct lf) =
    nd tagCase (nd (codedSubst repl i ct) lf)
  codedSubstTagged repl i (nd lf (nd lf (nd lf lf))) (nd ct (nd cu cv)) =
    nd tagCase (nd (codedSubst repl i ct)
                   (nd (codedSubst repl i cu)
                       (codedSubst repl (suc (suc i)) cv)))
  -- tag 4 = tagRec: recurse, step index shifts by 4
  codedSubstTagged repl i (nd lf (nd lf (nd lf (nd lf lf)))) lf =
    nd tagRec lf
  codedSubstTagged repl i (nd lf (nd lf (nd lf (nd lf lf)))) (nd ct lf) =
    nd tagRec (nd (codedSubst repl i ct) lf)
  codedSubstTagged repl i (nd lf (nd lf (nd lf (nd lf lf)))) (nd ct (nd cz cs)) =
    nd tagRec (nd (codedSubst repl i ct)
                  (nd (codedSubst repl i cz)
                      (codedSubst repl (suc (suc (suc (suc i)))) cs)))
  -- Unrecognized tags: return unchanged
  codedSubstTagged repl i (nd lf (nd lf (nd lf (nd lf (nd a b))))) payload =
    nd (nd lf (nd lf (nd lf (nd lf (nd a b))))) payload
  codedSubstTagged repl i (nd lf (nd lf (nd lf (nd (nd a b) c)))) payload =
    nd (nd lf (nd lf (nd lf (nd (nd a b) c)))) payload
  codedSubstTagged repl i (nd lf (nd lf (nd (nd a b) c))) payload =
    nd (nd lf (nd lf (nd (nd a b) c))) payload
  codedSubstTagged repl i (nd lf (nd (nd a b) c)) payload =
    nd (nd lf (nd (nd a b) c)) payload
  codedSubstTagged repl i (nd (nd a b) c) payload =
    nd (nd (nd a b) c) payload

------------------------------------------------------------------------
-- Specialized: substitute for variable 0.

codedSubst0 : Tree -> Tree -> Tree
codedSubst0 repl code = codedSubst repl zero code
