module Data.List.Kleene where

-- This module provides a different definition of lists based on the kleene
-- star and plus.

mutual
  data _⋆ {a} (A : Set a) : Set a where
    []  : A ⋆
    [_] : A ⁺ → A ⋆

  infixr 5 _&_
  record _⁺ {a} (A : Set a) : Set a where
    inductive
    constructor _&_
    field
      head : A
      tail : A ⋆
open _⁺ public
