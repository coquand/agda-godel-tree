{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA2.CorCGBridge
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
-- BRA2.Cor.corOfReify (codeFormula G) the bridge falls out
-- immediately.

module BRA2.CorCGBridge where

open import BRA2.Base
open import BRA2.Term
open import BRA2.Formula
open import BRA2.DerivThreshold
open import BRA2.Cor using (cor ; corOfReify)
open import BRA2.GoedelII using (cG ; G)

corCGBridge : Deriv (atomic (eqn (ap1 cor cG) (reify (code cG))))
corCGBridge = corOfReify (codeFormula G) (codeFormula_isValue G)
