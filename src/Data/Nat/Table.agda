module Data.Nat.Table where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; [])
open import Function

Table : Set
Table = List ℕ

insert : ℕ → Table → Table
insert i [] = i ∷ []
insert i (x ∷ xs) = go id i x xs
  where
  go : (ℕ → ℕ) → ℕ → ℕ → Table → Table
  go k zero zero xs = k zero ∷ xs
  go k zero (suc x) xs = k zero ∷ x ∷ xs
  go k (suc i) zero xs = k zero ∷ insert i xs
  go k (suc i) (suc x) xs = go (suc ∘ k) i x xs

open import Data.Maybe as Maybe using (Maybe; just; nothing)

member : ℕ → Table → Maybe ℕ
member x xs = List.foldr go (const nothing) xs x
  where
  go : ℕ → (ℕ → Maybe ℕ) → ℕ → Maybe ℕ
  go zero ys zero = just zero
  go (suc y) ys zero = nothing
  go zero ys (suc x) = Maybe.map suc (ys x)
  go (suc y) ys (suc x) = go y ys x

private
  open import Relation.Binary.PropositionalEquality
  example₁ : List.foldr insert [] (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ []) ≡ (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
  example₁ = refl

  example₂ : member 3 (List.foldr insert [] (4 ∷ 3 ∷ 1 ∷ 0 ∷ 2 ∷ [])) ≡ just 3
  example₂ = refl
