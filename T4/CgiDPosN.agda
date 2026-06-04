{-# OPTIONS --safe --without-K --exact-split #-}

-- T4.CgiDPosN -- the number-code re-pointing of T4.CgiDPos : the POSITIVE leg
-- dPosN over the decoder  runProgN  ( T4.ParseN ) instead of  runProg .
-- Verbatim mirror : thm13_binary / codeFXeqY2 are generic in the Fun2, so only
-- runProg -> runProgN ( and runProg_eq -> runProgN_eq ) change.

module T4.CgiDPosN where

open import T4.Base
open import T4.Tags using ( tag_eq ; tag_ap1 ; tag_ap2 ; tag_s )
open import T4.Code using ( codeFun1 ; codeFun2 )
open import T4.Num  using ( num ; num_at_S )
open import T4.ThmT using ( thmT )
open import T4.DefWit using ( cEqTm )
open import T4.EvalUEval using ( evalU )
open import T4.ParseN using ( parseN ; runProgN ; runProgN_eq )
open import T4.Thm12.Thm13 using ( codeFXeqY2 ; thm13_binary )
open import T4.Thm12.All using ( thm12_Fun2 ; fst )

------------------------------------------------------------------------
-- Local codeTerm-shape constructors ( match T4.CgiClash ).

cAp1f : Fun1 -> Term -> Term
cAp1f f t = ap2 Pair (natCode tag_ap1) (ap2 Pair (codeFun1 f) t)

cAp2f : Fun2 -> Term -> Term -> Term
cAp2f g a b = ap2 Pair (natCode tag_ap2) (ap2 Pair (codeFun2 g) (ap2 Pair a b))

------------------------------------------------------------------------
-- The closed definability code  DN  ( runProgN -headed ).

module _ (gL n0 x' : Term) where

  DN : Term
  DN = cEqTm (cAp2f runProgN (ap1 num gL) (ap1 num n0)) (cAp1f s (ap1 num x'))

------------------------------------------------------------------------
-- dPosN : T proves  DN , built num-raw from the single run fact.

dPosN :
  (gL n0 x' : Term) ->
  Deriv (eqF (ap2 evalU (ap1 parseN gL) n0) (ap1 s x')) ->
  Deriv (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProgN)) gL n0)) (DN gL n0 x'))
dPosN gL n0 x' rf =
  let run : Deriv (eqF (ap2 runProgN gL n0) (ap1 s x'))
      run = ruleTrans (runProgN_eq gL n0) rf

      d1 : Deriv (eqF (ap1 thmT (ap2 (fst (thm12_Fun2 runProgN)) gL n0))
                      (codeFXeqY2 runProgN gL n0 (ap1 s x')))
      d1 = thm13_binary runProgN gL n0 (ap1 s x') run

      bridge : Deriv (eqF (codeFXeqY2 runProgN gL n0 (ap1 s x')) (DN gL n0 x'))
      bridge = congR Pair (natCode tag_eq)
                 (congR Pair (cAp2f runProgN (ap1 num gL) (ap1 num n0)) (num_at_S x'))
  in ruleTrans d1 bridge
