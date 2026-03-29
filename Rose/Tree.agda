{-# OPTIONS --safe --without-K --exact-split #-}

module Rose.Tree where

------------------------------------------------------------------------
-- Binary trees: the only data type of the object system.

data Tree : Set where
  lf : Tree
  nd : Tree -> Tree -> Tree
