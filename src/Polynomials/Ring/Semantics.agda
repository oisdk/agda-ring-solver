{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_; foldr)
open import Level using (lift)
open import Data.Product

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


⟦_δ_∷_⟧ : Carrier → ℕ → Carrier → Carrier → Carrier
⟦ x δ i ∷ xs ⟧ ρ = (x + xs * ρ) * ρ ^ i

mutual
  Σ⟦_π_⟧ : ∀ {i n} → Coeffs i → suc i ≤ n → Vec Carrier n → Carrier
  Σ⟦ xs π m≤m ⟧ (ρ ∷ Ρ) = foldr (λ { (x ≠0 Δ i) xs → ⟦ ⟦ x ⟧ Ρ δ i ∷ xs ⟧ ρ }) 0# xs
  Σ⟦ xs π ≤-s i≤n ⟧ (_ ∷ Ρ) = Σ⟦ xs π i≤n ⟧ Ρ

  ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
  ⟦ Κ x  Π i≤n ⟧ _ = ⟦ x ⟧ᵣ
  ⟦ Σ xs Π i≤n ⟧ Ρ = Σ⟦ xs π i≤n ⟧ Ρ
