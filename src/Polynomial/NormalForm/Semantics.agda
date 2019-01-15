{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

-- "Evaluating" a polynomial, using Horner's method.

module Polynomial.NormalForm.Semantics
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat     using (ℕ; suc; zero)
open import Data.Vec     using (Vec; []; _∷_)
open import Data.List    using ([]; _∷_)
open import Data.Product using (_,_; _×_)

open import Polynomial.NormalForm.InjectionIndex
open Homomorphism homo
open import Polynomial.NormalForm.Definition coeffs

open import Polynomial.Exponentiation rawRing

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

{-# INLINE _⟦∷⟧_ #-}
