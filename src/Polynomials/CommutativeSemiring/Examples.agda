module Polynomials.CommutativeSemiring.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties
open import Polynomials.CommutativeSemiring.Expr Data.Nat.Properties.commutativeSemiring ℕ._≟_
open import Algebra using (CommutativeSemiring)
open CommutativeSemiring Data.Nat.Properties.commutativeSemiring
open import Relation.Binary.PropositionalEquality using (_≡_)

lem3 : (x : ℕ) → (2 * (x + 4) ≡ 8 + 2 * x)
lem3 = solve 1 (λ x' → Κ 2 ⊗ (x' ⊕ Κ 4) ⊜ Κ 8 ⊕ Κ 2 ⊗ x') refl

lem5 : (x y z : ℕ) → z + (x + y) ≡ x + 0 + 0 + z + 0 + y
lem5 = solve 3 (λ x y z → z ⊕ (x ⊕ y) ⊜ x ⊕ Κ 0 ⊕ Κ 0 ⊕ z ⊕ Κ 0 ⊕ y) refl

lem6 : (a b c d e f g h i : ℕ)
     → a * (b + (c * (d + (e * (f + (g * (h + i)))))))
     ≡ a * (b + (c * (d + (e * (f + (g * (h))))))) + a * (c * 1 * e) * g * i
lem6 = solve 9
  (λ a b c d e f g h i →
  a ⊗ (b ⊕ (c ⊗ (d ⊕ (e ⊗ (f ⊕ (g ⊗ (h ⊕ i))))))) ⊜
  a ⊗ (b ⊕ (c ⊗ (d ⊕ (e ⊗ (f ⊕ (g ⊗ h))))))
  ⊕ a ⊗ (c ⊗ Κ 1 ⊗ e) ⊗ g ⊗ i) refl
