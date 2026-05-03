{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA.CorCGBridge
--
-- The bridge equation
--
--    Deriv (atomic (eqn (ap1 cor cG) (reify (code cG))))
--
-- needed when soundified mp dispatchers consume an inner-check
-- witness whose RHS is in  codeFTeq*Hyp f x cG  form (containing
--  ap1 cor cG ) and the consuming target uses the closed form
--  reify (code cG)  (= the literal numeral of the Goedel sentence's
-- code).  cG is definitionally  reify (codeFormula G) , so by
-- BRA.Cor.corOfReify (codeFormula G) the bridge falls out
-- immediately.

module BRA.CorCGBridge where

open import BRA.Base
open import BRA.Term
open import BRA.Formula
open import BRA.Deriv
open import BRA.Cor using (cor ; corOfReify)
open import BRA.GoedelII using (cG ; G)

corCGBridge : Deriv (atomic (eqn (ap1 cor cG) (reify (code cG))))
corCGBridge = corOfReify (codeFormula G)
