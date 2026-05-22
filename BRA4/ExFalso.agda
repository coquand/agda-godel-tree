{-# OPTIONS --safe --without-K --exact-split #-}

-- BRA4.ExFalso -- the classical principle  P, ~P |- Q  for any Q .
--
-- Proof.  Use  axNeg Q P : (~Q -> ~P) -> (P -> Q)  and  axK (~P) (~Q)
-- to package  Deriv (~P)  as  Deriv (~Q -> ~P) , then  mp  twice.

module BRA4.ExFalso where

open import BRA4.Base

exFalso : (P Q : Formula) -> Deriv P -> Deriv (neg P) -> Deriv Q
exFalso P Q dP dNP =
  let
    -- axK (neg P) (neg Q) : Deriv (imp (neg P) (imp (neg Q) (neg P))) .
    k : Deriv (imp (neg P) (imp (neg Q) (neg P)))
    k = axK (neg P) (neg Q)

    -- mp k dNP : Deriv (imp (neg Q) (neg P)) .
    impNegQNegP : Deriv (imp (neg Q) (neg P))
    impNegQNegP = mp k dNP

    -- axNeg Q P : Deriv (imp (imp (neg Q) (neg P)) (imp P Q)) .
    ax : Deriv (imp (imp (neg Q) (neg P)) (imp P Q))
    ax = axNeg Q P

    impPQ : Deriv (imp P Q)
    impPQ = mp ax impNegQNegP
  in mp impPQ dP
