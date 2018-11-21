{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_)
open import Level using (lift)
open import Data.Product
open import Polynomial.Normal.Parameters

module Polynomial.Normal.Semantics
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat.Order.Gappy
open Homomorphism homo
open import Polynomial.Normal.Definition coeffs

-- Exponentiation
infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero = 1#
x ^ suc n = x * x ^ n

drop : ∀ {i n} → i ≤′ n → Vec Carrier n → Vec Carrier i
drop ≤′-refl Ρ = Ρ
drop (≤′-step si≤n) (_ ∷ Ρ) = drop si≤n Ρ

vec-uncons : ∀ {n} → Vec Carrier (suc n) → Carrier × Vec Carrier n
vec-uncons (x ∷ xs) = x , xs

drop-1 : ∀ {i n} → suc i ≤′ n → Vec Carrier n → Carrier × Vec Carrier i
drop-1 si≤n xs = vec-uncons (drop si≤n xs)

mutual
  _⟦∷⟧_ : ∀ {n} → Poly n × Coeffs n → Carrier × Vec Carrier n → Carrier
  (x , xs) ⟦∷⟧ (ρ , ρs) = ⟦ x ⟧ ρs + Σ⟦ xs ⟧ (ρ , ρs) * ρ

  Σ⟦_⟧ : ∀ {n} → Coeffs n → (Carrier × Vec Carrier n) → Carrier
  Σ⟦ x ≠0 Δ i ∷ xs ⟧ (ρ , ρs) = (x , xs) ⟦∷⟧ (ρ , ρs) * ρ ^ i
  Σ⟦ [] ⟧ _ = 0#

  ⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
  ⟦ Κ x  Π i≤n ⟧ _ = ⟦ x ⟧ᵣ
  ⟦ Σ xs Π i≤n ⟧ Ρ = Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
