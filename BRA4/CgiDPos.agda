{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.CgiDPos -- CGI num-raw step (c): the POSITIVE leg  dPos , single-conjunct.
--
-- definable is ONE equation (surprise.pdf: "p outputs x and stops"):
--   definable p x n = evalU(parse p, n) = s x .
-- From the run fact (g outputs x' at fuel n0 -- DERIVED from the loop, here a
-- hypothesis  rf ), internalise it num-raw via  thm13_binary / codeFXeqY2  on the
-- single Fun2  runProg , bridging the codeFXeqY2 RHS  num (s x')  to the
-- substitution-form  code(s)(num x')  by  num_at_S .  The result is SYNTACTICALLY
-- D = the closed  definable  code that the instantiated open  dNeg  carries
-- (program/fuel slots by refl, RHS by the single num_at_S bridge).

module BRA4.CgiDPos where

open import BRA4.Base
open import BRA4.Tags using ( tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import BRA4.Code using ( codeFun1 ; codeFun2 )
open import BRA4.Num  using ( num ; num_at_S )
open import BRA4.ThmT using ( thmT )
open import BRA4.DefWit using ( cEqTm )
open import BRA4.EvalUEval using ( evalU )
open import BRA4.ProgParse using ( parse )
open import BRA4.Kdef using ( runProg ; runProg_eq )
open import BRA4.Thm12.Thm13 using ( codeFXeqY2 ; thm13_binary )
open import BRA4.Thm12.All using ( thm12_Fun2 ; fst )

------------------------------------------------------------------------
-- Local codeTerm-shape constructors (match BRA4.Kdef / CgiClash).

cAp1f : Fun1 -> Term -> Term
cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

cAp2f : Fun2 -> Term -> Term -> Term
cAp2f g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

------------------------------------------------------------------------
-- The closed definability code  D  (= codeFormula (definable (var0) x' (var1))
-- num-headed, with  var0 := num gL , var1 := num n0  dropped raw).

module _ (gL n0 x' : Term) where

  D : Term
  D = cEqTm (cAp2f runProg (ap1 num gL) (ap1 num n0)) (cAp1f s (ap1 num x'))

------------------------------------------------------------------------
-- dPos : T proves  D , built num-raw from the single run fact.

dPos :
  (gL n0 x' : Term) ->
  Deriv (eqF (ap2 evalU (ap1 parse gL) n0) (ap1 s x')) ->   -- the halt fact (g outputs x' at n0)
  Deriv (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProg)) gL n0)) (D gL n0 x'))
dPos gL n0 x' rf =
  let run : Deriv (eqF (ap2 runProg gL n0) (ap1 s x'))
      run = ruleTrans (runProg_eq gL n0) rf

      d1 : Deriv (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProg)) gL n0))
                      (codeFXeqY2 runProg gL n0 (ap1 s x')))
      d1 = thm13_binary runProg gL n0 (ap1 s x') run

      -- bridge  codeFXeqY2 runProg gL n0 (s x') = D  (RHS  num (s x') -> code(s)(num x')).
      bridge : Deriv (eqF (codeFXeqY2 runProg gL n0 (ap1 s x')) (D gL n0 x'))
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp2f runProg (ap1 num gL) (ap1 num n0)) (num_at_S x'))
  in ruleTrans d1 bridge
