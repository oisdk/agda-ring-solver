{-# OPTIONS --without-K #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
NatRing : ACR.AlmostCommutativeRing Level.zero Level.zero
NatRing = ACR.fromCommutativeSemiring *-+-commutativeSemiring
open ACR.AlmostCommutativeRing NatRing
open import Polynomials.Ring.Reflection NatRing ℕ._≟_
open import Function
open import Reflection
import Data.Fin as Fin

lem3 : Set
lem3 = (x : ℕ) → 0 + x ≡ x

ex3 : Term
ex3 = quoteTerm (Expr ℕ 0 ∋ Κ 1# ⊕ Κ 1#)

ex4 : Term
ex4 = toExpr 0 (quoteTerm (1# + 1#))

ex5 : Expr ℕ ℕ.zero
ex5 = qExpr (1# + 1#)

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
