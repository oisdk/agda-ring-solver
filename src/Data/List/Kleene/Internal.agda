{-# OPTIONS --without-K --safe #-}

module Data.List.Kleene.Internal where

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

infixr 5 _∹_
pattern _∹_ x xs = [ x & xs ]

module _ {a b} {A : Set a} {B : Set b} (f : A → B → B) (b : B) where
  mutual
    foldr⁺ : A ⁺ → B
    foldr⁺ (x & xs) = f x (foldr⋆ xs)

    foldr⋆ : A ⋆ → B
    foldr⋆ [] = b
    foldr⋆ [ xs ] = foldr⁺ xs

-- Why is this useful? What does it give us over the normal list definition?
--
-- As is explained in the report, one of the most import factors which gives
-- us a speedup in the solver is *avoiding identities*. For instance, in
-- Haskell, we might write foldMap like this (on lists):
--
--   foldMap _ [] = mempty
--   foldMap f (x:xs) = f x <> foldMap f xs
--
-- To avoid mempty, we could instead write this:
--
--   foldMap _ [] = mempty
--   foldMap f [x] = f x
--   foldMap f (x:xs) = f x <> foldMap f xs
--
-- This avoids a mempty on nonempty lists, but does an extra pattern match.
-- For these lists, we can write:
open import Algebra

module _ {m r} (mon : RawMonoid m r) where
  open RawMonoid mon

  foldMap : ∀ {a} {A : Set a} → (A → Carrier) → A ⋆ → Carrier
  foldMap f [] = ε
  foldMap {A = A} f [ xs ] = go xs
    where
    go : A ⁺ → Carrier
    go (x & []) = f x
    go (x & [ xs ]) = f x ∙ go xs
-- Which is a little cleaner.
