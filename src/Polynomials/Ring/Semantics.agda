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

drop : ∀ {i n} → i ≤ n → Vec Carrier n → Vec Carrier i
drop m≤m Ρ = Ρ
drop (≤-s si≤n) (_ ∷ Ρ) = drop si≤n Ρ

vec-uncons : ∀ {n} → Vec Carrier (suc n) → Carrier × Vec Carrier n
vec-uncons (x ∷ xs) = x , xs

drop-1 : ∀ {i n} → suc i ≤ n → Vec Carrier n → Carrier × Vec Carrier i
drop-1 si≤n xs = vec-uncons (drop si≤n xs)

mutual
  ⌊_⌋⟦_δ_∷_⟧ : ∀ {n} → ⌊ n ⌋ → Poly n → ℕ → (Carrier × Vec Carrier n → Carrier) → Carrier × Vec Carrier n → Carrier
  ⌊ a ⌋⟦ x δ i ∷ xs ⟧ (ρ , Ρ) = (⌊ a ⌋⟦ x ⟧ Ρ + xs (ρ , Ρ) * ρ) * ρ ^ i

  ⌊_⌋Σ⟦_⟧ : ∀ {n} → ⌊ n ⌋ → Coeffs n → (Carrier × Vec Carrier n) → Carrier
  ⌊ a ⌋Σ⟦ xs ⟧ = foldr (λ { (x ≠0 Δ i) xs → ⌊ a ⌋⟦ x δ i ∷ xs ⟧ }) (λ _ → 0#) xs

  ⌊_⌋⟦_⟧ : ∀ {n} → ⌊ n ⌋ → Poly n → Vec Carrier n → Carrier
  ⌊ _ ⌋⟦ Κ x  Π i≤n ⟧ _ = ⟦ x ⟧ᵣ
  ⌊ acc wf ⌋⟦ Σ xs Π i≤n ⟧ Ρ = ⌊ wf _ i≤n ⌋Σ⟦ xs ⟧ (drop-1 i≤n Ρ)


⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦_⟧ = ⌊ ⌊↓⌋ ⌋⟦_⟧
