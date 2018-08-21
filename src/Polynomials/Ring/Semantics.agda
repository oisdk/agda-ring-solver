{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List)
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


drop : ∀ {i n} → i ℕ.≤″ n → Vec Carrier n → Vec Carrier i
drop (ℕ.less-than-or-equal {k = k} proof) xs = {!!}

-- Evaluation
⟦_⟧ : ∀ {n} → Poly n → Vec Carrier n → Carrier
⟦ i≤n Π Κ x  ⟧ Ρ = ⟦ x ⟧ᵣ
⟦ i≤n Π Σ xs ⟧ Ρ = {!!}

-- ⟦_⟧ (i≤n Π Σ xs) Ρ = List.foldr coeff-eval 0# xs
--   where
--   coeff-eval : Coeff n × ℕ → Carrier → Carrier
--   coeff-eval (c ,~ _ , p) xs = (⟦ c ⟧ ρ + xs * y) * y ^ p

