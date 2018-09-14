{-# OPTIONS --without-K #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
import Level
open import Relation.Binary.PropositionalEquality using (_≡_)
NatRing : ACR.AlmostCommutativeRing Level.zero Level.zero
NatRing = ACR.fromCommutativeSemiring *-+-commutativeSemiring
open ACR.AlmostCommutativeRing NatRing
open import Polynomials.Ring.Reflection NatRing ℕ._≟_

lem3 : genExpr (2 + 2) ≡ Κ 2 ⊕ Κ 2
lem3 = autosolve

-- lem5 : (x y z : ℕ) → z + (x + y) ≡ x + 0 + 0 + z + 0 + y
-- lem5 = solve 3 (λ x y z → z ⊕ (x ⊕ y) ⊜ x ⊕ Κ 0 ⊕ Κ 0 ⊕ z ⊕ Κ 0 ⊕ y) refl

-- lem6 : (a b c d e f g h i : ℕ)
--      → a * (b + (c * (d + (e * (f + (g * (h + i)))))))
--      ≡ a * (b + (c * (d + (e * (f + (g * (h))))))) + a * (c * 1 * e) * g * i
-- lem6 = solve 9
--   (λ a b c d e f g h i →
--   a ⊗ (b ⊕ (c ⊗ (d ⊕ (e ⊗ (f ⊕ (g ⊗ (h ⊕ i))))))) ⊜
--   a ⊗ (b ⊕ (c ⊗ (d ⊕ (e ⊗ (f ⊕ (g ⊗ h))))))
--   ⊕ a ⊗ (c ⊗ Κ 1 ⊗ e) ⊗ g ⊗ i) refl
