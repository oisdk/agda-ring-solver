{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_)
open import Level using (lift)
open import Data.Product
open import Data.Product.Irrelevant

module Polynomials.Ring.Semantics
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  where

open AlmostCommutativeRing ring
open import Polynomials.Ring.Normal coeff Zero-C zero-c?
open _-Raw-AlmostCommutative⟶_ morphism using () renaming (⟦_⟧ to ⟦_⟧ᵣ)

-- Exponentiation
infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

drop : ∀ {i n} → i ≤ n → Vec Carrier n → Vec Carrier i
drop m≤m xs = xs
drop (≤-s i≤n) (_ ∷ xs) = drop i≤n xs

mutual
  Σ⟦_⟧ : ∀ {n} → Coeffs n →  Carrier → Vec Carrier n → Carrier
  Σ⟦ c ≠0 Δ i ∷ xs ⟧ ρ Ρ = (⟦ c ⟧ Ρ + Σ⟦ xs ⟧ ρ Ρ * ρ) * ρ ^ i
  Σ⟦ [] ⟧ _ _ = 0#

  -- Evaluation
  ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
  ⟦ Κ x  Π i≤n ⟧ _ = ⟦ x ⟧ᵣ
  ⟦ Σ xs Π i≤n ⟧ Ρ with drop i≤n Ρ
  ... | (ρ ∷ Ρ′) = Σ⟦ xs ⟧ ρ Ρ′

