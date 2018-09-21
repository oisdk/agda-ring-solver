{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_; foldr)
open import Level using (lift)
open import Data.Product
open import Function

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

data VecAcc (n : ℕ) : Set r₃ where
  stop : (∀ {m} → suc m ≤ n → Carrier × VecAcc m) → VecAcc n

vec-drop : ∀ {m n} → Vec Carrier n → suc m ≤ n → Carrier × VecAcc m
vec-drop (x ∷ xs) m≤m = x , stop (vec-drop xs)
vec-drop (x ∷ xs) (≤-s sm≤n) = vec-drop xs sm≤n

⟦_δ_∷_⟧ : Carrier → ℕ → Carrier → Carrier → Carrier
⟦ x δ i ∷ xs ⟧ ρ = (x + xs * ρ) * ρ ^ i

mutual
  Σ⟦_⟧ : ∀ {n} → Coeffs n → (Carrier × VecAcc n) → Carrier
  Σ⟦ xs ⟧ (ρ , Ρ) = foldr (λ { (x ≠0 Δ i) xs → ⟦ Π⟦ x ⟧ Ρ δ i ∷ xs ⟧ ρ }) 0# xs

  Π⟦_⟧ : ∀ {n} → Poly n → VecAcc n → Carrier
  Π⟦ Κ x  Π i≤n ⟧ _ = ⟦ x ⟧ᵣ
  Π⟦ Σ xs Π i≤n ⟧ (stop ρ) = Σ⟦ xs ⟧ (ρ i≤n)

⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦ xs ⟧ ρ = Π⟦ xs ⟧ (stop (vec-drop ρ))
